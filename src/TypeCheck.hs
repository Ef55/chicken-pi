{- pi-forall -}

{-# HLINT ignore "Use forM_" #-}

-- | The main routines for type-checking
module TypeCheck (tcModules, inferType, checkType) where

import Control.Exception (assert)
import Control.Monad.Except
import Data.Maybe (catMaybes, fromMaybe)
import Debug.Trace
import Environment (D (..), TcMonad)
import Environment qualified as Env
import Equal qualified
import PrettyPrint (D (..), Disp (disp), debug, pp)
import Syntax
import Text.PrettyPrint.HughesPJ (render, ($$))
import Unbound.Generics.LocallyNameless (string2Name)
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold qualified as Unbound
import Unbound.Generics.LocallyNameless.Unsafe qualified as Unbound

---------------------------------------------------------------------

-- | Subtyping relation to handle universe cumulativity
-- From https://coq.inria.fr/doc/master/refman/language/cic.html#subtyping-rules
isSubtype :: Type -> Type -> TcMonad ()
isSubtype l r = do
  l' <- Equal.whnf l
  r' <- Equal.whnf r
  subtype l' r'
  where
    subtype :: Type -> Type -> TcMonad ()
    subtype (TyType l1) (TyType l2) =
      case (l1, l2) of
        -- Rule 1
        _ | l1 == l2 -> return ()
        -- Rule 2
        (LConst i, LConst j) | i <= j -> return ()
        -- Rule 3
        (LSet, LConst _) -> return ()
        -- Rule 4; Theory and practice disagree here...
        (LProp, _) -> return ()
        _ -> err
      where
        err =
          Env.cerr
            [ DS "Universe level mismatch: cannot use",
              DD l1,
              DS "where",
              DD l2,
              DS "is expected."
            ]
    -- Rule 5; not supported (yet) due to lack of use-cases
    -- Rule 6; not covered, we don't support universe polymorphism
    -- We take the symmetric closure to ease implementation
    subtype ty1 ty2 = Equal.equate ty1 ty2

-- | Infer/synthesize the type of a term
inferType :: Term -> TcMonad Type
inferType a = case a of
  -- i-var
  (Var x) -> do
    decl <- Env.lookupTy x
    return (declType decl)

  -- i-type -- Type l : Type (l + 1)
  TyType l -> return (TyType (levelAdd l 1))
  -- i-pi

  (TyPi tyA bnd) -> do
    (x, tyB) <- unbind bnd
    l1 <- tcType tyA -- Ensure tyA is a valid type and get its level
    Env.extendCtx (Decl (TypeDecl x tyA)) $ do
      tyB' <- Equal.whnf tyB
      l2 <- tcType tyB'
      l <- case (l1, l2) of
        -- Prod-Prop
        (_, LProp) -> return LProp
        -- Prod-Set
        (LProp, LSet) -> return LSet
        (LSet, LSet) -> return LSet
        -- Prod-Type (with subtyping builtin)
        (LConst i, LConst j) -> return $ LConst (max i j)
        (_, LConst _) -> return l2
        (LConst _, _) -> return l1
      return (TyType l) -- Pi types are in universe level 'l'

  -- i-app
  (App a b) -> do
    ty1 <- inferType a
    ty1' <- Equal.whnf ty1
    case ty1' of
      (TyPi tyA bnd) -> do
        checkType b tyA
        return (instantiate bnd b)
      (Guarded x (TyPi tyA bnd)) -> do
        checkType b tyA
        structurallySmaller x b
        return (instantiate bnd b)
      _ -> Env.err [DS "Expected a function type but found", DD a, DS "of type", DD ty1]

  -- i-ann
  (Ann a tyA) -> do
    ensureType tyA
    checkType a tyA
    return tyA

  -- Practicalities
  -- remember the current position in the type checking monad
  (Pos p a) ->
    Env.extendSourceLocation p a $ inferType a
  -- Extensions to the core language

  -- i-sigma
  (TySigma tyA bnd) -> do
    (x, tyB) <- unbind bnd
    l1 <- tcType tyA
    Env.extendCtx (mkDecl x tyA) $ do
      l2 <- tcType tyB
      let l = case (l1, l2) of
            (_, LProp) -> LProp
            (_, LSet) -> LSet
            (LConst i, LConst j) -> LConst (max i j)
            (LProp, l) -> l
            (LSet, l) -> l
      return (TyType l) -- Sigma types are in universe level 'l'

  -- i-eq
  (TyEq a b) -> do
    aTy <- inferType a
    checkType b aTy
    return (TyType LProp)
  (Case scrut pred branches) -> checkCase scrut pred branches Nothing
  _ ->
    Env.err [DS "Must have a type annotation for", DD a]

-------------------------------------------------------------------------

isEmptyOrSingleton :: TypeConstructor -> TcMonad Bool
isEmptyOrSingleton (TypeConstructor _ pack) = do
  (_, (_, constructors)) <- Unbound.unbind pack
  return $ case constructors of
    [] -> True -- Empty type
    [_] -> True -- Singleton type
    _ -> False -- More than one constructor

structurallySmaller :: TName -> Term -> TcMonad ()
structurallySmaller p t = do
  t' <- Equal.whnf t
  case t' of
    Var n -> do
      decreasing <- Env.lookupSmaller (Var p) n
      unless decreasing err
    App l _ -> structurallySmaller p l
    Lam bnd -> do
      (_, body) <- Unbound.unbind bnd
      structurallySmaller p body
    _ -> err

  where
    err :: TcMonad () = do
      gamma <- Env.getLocalCtx
      Env.err
        [ DS "Recursive calls requires",
          DD t,
          DS "to be structurally smaller than",
          DD p,
          DS "which could not be ensured. Context:",
          DD gamma
        ]

-------------------------------------------------------------------------

checkCase :: Term -> DestructionPredicate -> [Branch] -> Maybe Type -> TcMonad Type
checkCase scrut pred branches mRet = do
  (typeDecl, typeParams, pred, ret) <- checkScrutinee scrut pred mRet
  checkMatch scrut pred typeDecl typeParams branches
  return ret

instantiateDestructionPredicate :: Term -> [Type] -> Unbound.Bind (TName, Pattern) Type -> TcMonad Type
instantiateDestructionPredicate scrut typeArgs pred = do
  ((sVar, PatCon _ typeArgVars), res) <- Unbound.unbind pred
  when (length typeArgVars /= length typeArgs) $
    Env.err
      [ DS "Internal error: instantiateDestructionPredicate.",
        DS "Vars:",
        DL $ DD <$> typeArgVars,
        DS "Args:",
        DL $ DD <$> typeArgs
      ]
  return $ Unbound.substs ((sVar, scrut) : zip typeArgVars typeArgs) res

checkScrutinee ::
  Term ->
  DestructionPredicate ->
  Maybe Type ->
  TcMonad (TypeConstructor, [Type], Unbound.Bind (TName, Pattern) Type, Type)
checkScrutinee s p@(DestructionPredicate bPred) mExp = do
  -- Dummy term used for error reporting
  let dummy = Case s p []

  -- Check scrutinee and extract information about its type
  sType <- inferType s
  (typeCstrName, typeArgs) <- Equal.unconstruct sType
  tcLookup <- Env.lookupTypeConstructor typeCstrName
  typeDecl <- case tcLookup of
    Just tcDecl -> return tcDecl
    Nothing ->
      Env.err
        [ DS "The scrutinee in",
          DD dummy,
          DS "has type",
          DD sType,
          DS "which is not a datatype."
        ]
  (typeParams, _) <- splitParamsIndices typeDecl typeArgs

  -- Generate a full destruction predicate
  ((asBind, inBind), mRet) <- Unbound.unbind bPred
  asBind' <- maybe Env.freshWildcard return asBind
  inBind' <- maybe (generatePattern typeCstrName typeArgs) return inBind
  paraRet <- case (mRet, mExp) of
    (Just ret, _) -> return ret
    (_, Just ret) -> return ret
    (Nothing, Nothing) ->
      Env.err
        [ DS "Cannot infer return type of case expression",
          DD dummy
        ]
  let pred = Unbound.bind (asBind', inBind') paraRet

  -- Check expected type against destruction predicate
  ret <- instantiateDestructionPredicate s typeArgs pred
  case mExp of
    Nothing -> return ()
    Just exp -> Equal.equate exp ret

  scrutKind <- inferType sType
  singletonScrut <- isEmptyOrSingleton typeDecl
  -- Should check the kind of the whole destruction predicate,
  -- not just the kind of the instantiated predicate. I don't think that changes
  -- anything, but that's what the theory says. 
  retKind <- inferType ret
  when (aeq scrutKind (TyType LProp) && not singletonScrut && not (aeq retKind (TyType LProp))) $
    Env.err
      [ DS "Scrutinee",
        DD s,
        DS "of kind",
        DD scrutKind,
        DS "cannot be eliminated into type",
        DD ret,
        DS "which has type",
        DD retKind
      ]

  -- Check that the "decoration" at the start of the in clause
  -- matches the type being destructed.
  case inBind' of
    PatCon name _ ->
      unless (string2Name name == typeCstrName) $
        Env.err
          [ DS "The type mentioned in the 'in' clause",
            DD inBind',
            DS "should be headed by",
            DD typeCstrName,
            DS "because that's the type of the scrutinee."
          ]

  return (typeDecl, typeParams, pred, ret)
  where
    generatePattern :: TName -> [Type] -> TcMonad Pattern
    generatePattern typeCstrName typeArgs = PatCon (Unbound.name2String typeCstrName) <$> mapM (const Env.freshWildcard) typeArgs

    splitParamsIndices :: TypeConstructor -> [Type] -> TcMonad ([Type], [Type])
    splitParamsIndices (TypeConstructor _ pack) args = do
      (telescope, _) <- Unbound.unbind pack
      let params :: [TName] = Unbound.toListOf Unbound.fv telescope
          paramCount = length params
      return $ splitAt paramCount args

checkMatch :: Term -> Unbound.Bind (TName, Pattern) Type -> TypeConstructor -> [Type] -> [Branch] -> TcMonad ()
checkMatch scrut ret (TypeConstructor typeName pack) typeParams branches = do
  (_, (_, constructors)) <- instantiateTelescope pack typeParams

  when (length branches /= length constructors) $
    Env.err
      [ DS $ "Pattern matching has " ++ show (length branches) ++ " branches, yet the matched type",
        DD typeName,
        DS $ "has " ++ show (length constructors) ++ " constructors."
      ]
  mapM_ (uncurry (checkBranch scrut ret typeParams)) (zip constructors branches)

checkBranch :: Term -> Unbound.Bind (TName, Pattern) Type -> [Type] -> Constructor -> Branch -> TcMonad ()
checkBranch concreteScrut retPred typeParams cstr@(Constructor cstrName recComponents cstrType) (Branch branch) = do
  (pat@(PatCon cstrStr xs), body) <- Unbound.unbind branch
  when (cstrName /= string2Name cstrStr) $
    Env.err
      [ DS "Pattern is headed by",
        DD cstrStr,
        DS "but constructor",
        DD cstrName,
        DS "was expected."
      ]

  let cstrVars = Var <$> xs
      cstrArgs = typeParams ++ cstrVars
      abstractScrut = foldl App (Var cstrName) cstrArgs
  typeArgs <- Equal.instantiateConstructorType cstrName cstrArgs
  ret <- instantiateDestructionPredicate abstractScrut typeArgs retPred

  -- Retrieve the type of the bindings in the telescope
  (telescope, _) <- instantiateTelescope cstrType cstrVars
  when (length xs /= length recComponents) $ Env.err [
      DL $ DD <$> xs, DS "|", DL $ DD <$> recComponents
    ]
  let typingEntries = zipWith (\x t -> Decl $ TypeDecl x t) xs telescope
      -- Add a "Smaller" entry for each recursive component
      smallerEntries = map (Smaller concreteScrut . snd) $ filter fst $ zip recComponents xs
      entries = typingEntries ++ smallerEntries

  when (length telescope /= length xs) $
    Env.err
      [ DS "Pattern",
        DD pat,
        DS "does not bind the correct number of variables for constructor",
        DD cstr
      ]
  Env.extendCtxs entries $ checkType body ret

-------------------------------------------------------------------------

-- | Make sure that the term is a "type" (i.e. that its type is a sort)
-- Returns its sort.
tcType :: Term -> TcMonad Level
tcType tm = do
  ty <- inferType tm
  ty' <- Equal.whnf ty
  tcSort ty'

-- | Ensure that a term is a "type" (i.e. that its type is a sort)
ensureType :: Term -> TcMonad ()
ensureType = void . tcType

-- | Make sure that the term is a sort
tcSort :: Term -> TcMonad Level
tcSort tm = do
  tm' <- Equal.whnf tm
  case tm' of
    TyType s -> return s
    _ -> Env.err [DS "Expected", DD tm', DS "to be a sort."]

arityOf :: Type -> TcMonad ([(TName, Type)], Type)
arityOf t = iter [] t
  where
    iter acc t =
      Equal.whnf t >>= \t' -> case t' of
        TyPi xType bnd -> do
          (x, body) <- Unbound.unbind bnd
          iter ((x, xType) : acc) body
        _ -> return (reverse acc, t)

isArityOfSort :: Type -> TcMonad Level
isArityOfSort t = do
  (_, t') <- arityOf t
  tcSort t'

isConstructorOf :: Type -> TName -> TcMonad ([(TName, Type)], [Term])
isConstructorOf t typ = do
  (bnds, t') <- arityOf t
  (h, args) <- Equal.unconstruct t'
  unless (h == typ) $ Env.err [DS "The constructor has type", DD t', DS "expected a constructor for", DD typ]
  return (bnds, args)

-------------------------------------------------------------------------

-- | Check that the given term has the expected type
checkType :: Term -> Type -> TcMonad ()
checkType tm ty = do
  ty' <- Equal.whnf ty
  case tm of
    -- c-lam: check the type of a function
    (Lam bnd) -> case ty' of
      (TyPi tyA bnd2) -> do
        -- unbind variables and check the body
        (x, body, tyB) <- unbind2 bnd bnd2
        ensureType tyA
        Env.extendCtx (Decl (TypeDecl x tyA)) $ do
          ensureType tyB
          -- Check the body
          checkType body tyB
        return ()
      _ -> Env.err [DS "Lambda expression should have a function type, not", DD ty']
    (Fix bnd) -> do
      ((self, xs), bnd') <- Unbound.unbind bnd
      (paramTypes, ty'') <- introBindings xs [] ty'
      case ty'' of
        (TyPi tyA bnd2) -> do
          -- unbind the variables in the lambda expression and pi type
          (x, body, tyB) <- unbind2 bnd' bnd2
          -- check the type of the body of the lambda expression
          let guardedTy =
                foldr
                  (\(x, t) r -> TyPi t $ Unbound.bind x r)
                  (Guarded x $ TyPi tyA $ Unbound.bind x tyB)
                  (zip xs paramTypes)
          -- Env.warn [DD ty', DS "|", DD guardedTy]
          Env.extendCtxs
            ( -- Add a binding for this recursive function...
              Decl (TypeDecl self guardedTy)
                -- ... another one for the recursive parameter...
                : Decl (TypeDecl x tyA)
                -- ... and for all the other parameters.
                : (Decl <$> zipWith TypeDecl xs paramTypes)
            )
            $ checkType body tyB
        _ -> Env.err [DS "Found type", DD ty'', DS "while fix still has to introduce its last argument."]
      where
        introBindings :: [TName] -> [Type] -> Type -> TcMonad ([Type], Type)
        introBindings [] acc r = return (reverse acc, r)
        introBindings (b : bs) acc r =
          case r of
            (TyPi tyA bnd) -> do
              r' <- Equal.whnf $ Unbound.instantiate bnd [Var b]
              introBindings bs (tyA : acc) r'
            _ -> Env.err [DS "Found type", DD r, DS "while fix still has to introduce", DD b]

    -- Practicalities
    (Pos p a) ->
      Env.extendSourceLocation p a $ checkType a ty'
    TrustMe -> Env.warn [DS "Unmet obligation."]
    PrintMe -> do
      gamma <- Env.getLocalCtx
      Env.warn
        [ DS "Unmet obligation.\nContext:",
          DD gamma,
          DS "\nGoal:",
          DD ty'
        ]
    -- Extensions to the core language
    -- c-prod
    (Prod a b) -> do
      case ty' of
        (TySigma tyA bnd) -> do
          (x, tyB) <- unbind bnd
          ensureType tyA
          checkType a tyA
          Env.extendCtxs [mkDecl x tyA, Def x a] $ do
            ensureType tyB
            checkType b tyB
        _ ->
          Env.err
            [ DS "Products must have Sigma Type",
              DD ty',
              DS "found instead"
            ]
    -- c-letpair
    (LetPair p bnd) -> do
      ((x, y), body) <- Unbound.unbind bnd
      pty <- inferType p
      pty' <- Equal.whnf pty
      case pty' of
        TySigma tyA bnd' -> do
          ensureType tyA
          let tyB = instantiate bnd' (Var x)
          Env.extendCtx (mkDecl x tyA) $ ensureType tyB
          decl <- Equal.unify [] p (Prod (Var x) (Var y))
          Env.extendCtxs ([mkDecl x tyA, mkDecl y tyB] ++ decl) $
            checkType body ty'
        _ -> Env.err [DS "Scrutinee of LetPair must have Sigma type"]
    -- c-let
    (Let a bnd) -> do
      (x, b) <- unbind bnd
      tyA <- inferType a
      ensureType tyA
      Env.extendCtxs [mkDecl x tyA, Def x a] $
        checkType b ty'
    -- c-refl
    Refl -> case ty' of
      (TyEq a b) -> Equal.equate a b
      _ -> Env.err [DS "Refl annotated with invalid type", DD ty']
    -- c-subst
    (Subst a b) -> do
      tp <- inferType b
      ensureType tp
      nf <- Equal.whnf tp
      (m, n) <- case nf of
        TyEq m n -> return (m, n)
        _ -> Env.err [DS "Subst requires an equality type, not", DD tp]
      inferType m >>= ensureType
      inferType n >>= ensureType
      edecl <- Equal.unify [] m n
      pdecl <- Equal.unify [] b Refl
      Env.extendCtxs (edecl ++ pdecl) $ checkType a ty'
    -- c-contra
    (Contra p) -> do
      ty_p <- inferType p
      nf <- Equal.whnf ty_p
      (a, b) <- case nf of
        TyEq m n -> return (m, n)
        _ -> Env.err [DS "Contra requires an equality type, not", DD ty_p]
      inferType a >>= ensureType
      inferType b >>= ensureType
      a' <- Equal.whnf a
      b' <- Equal.whnf b
      case (Equal.maybeUnconstruct a', Equal.maybeUnconstruct b') of
        (Just (c1, _), Just (c2, _)) -> do
          t1 <- Env.lookupConstructor c1
          t2 <- Env.lookupConstructor c2
          case (t1, t2) of
            (Just _, Just _) ->
              if c1 /= c2
                then return ()
                else
                  Env.err
                    [ DS "I can't tell that",
                      DD a',
                      DS "and",
                      DD b',
                      DS "are contradictory.",
                      DD c1,
                      DS "and",
                      DD c2,
                      DS "are the same constructor."
                    ]
            _ ->
              Env.err
                [ DS "I can't tell that",
                  DD a',
                  DS "and",
                  DD b',
                  DS "are contradictory.",
                  DD c1,
                  DS "or",
                  DD c2,
                  DS "is not a constructor."
                ]
        _ ->
          Env.err
            [ DS "I can't tell that",
              DD a',
              DS "and",
              DD b',
              DS "are contradictory"
            ]
    (Case scrut pred branches) -> void $ checkCase scrut pred branches (Just ty')
    -- c-infer
    _ -> do
      tyA <- inferType tm
      isSubtype tyA ty' -- Use subtype to handle universe cumulativity

--------------------------------------------------------
-- Using the typechecker for decls and modules and stuff
--------------------------------------------------------

-- | Typecheck a collection of modules. Assumes that each module
-- appears after its dependencies. Returns the same list of modules
-- with each definition typechecked
tcModules :: [Module] -> TcMonad [Module]
tcModules = foldM tcM []
  where
    -- Check module m against modules in defs, then add m to the list.
    defs `tcM` m = do
      -- "M" is for "Module" not "monad"
      m' <- defs `tcModule` m
      return $ defs ++ [m']

-- | Typecheck an entire module.
tcModule ::
  -- | List of already checked modules (including their entries).
  [Module] ->
  -- | Module to check.
  Module ->
  -- | The same module with all entries checked and elaborated.
  TcMonad Module
tcModule defs m' = do
  checkedEntries <-
    Env.extendCtxMods importedModules $
      foldr
        tcE
        (return [])
        (moduleEntries m')
  return $ m' {moduleEntries = checkedEntries}
  where
    d `tcE` m = do
      -- Extend the Env per the current Entry before checking
      -- subsequent entries.
      x <- tcEntry d
      case x of
        AddHint hint -> Env.extendHints hint m
        -- Add decls to the entries to be returned
        AddCtx decls -> (decls ++) <$> Env.extendCtxsGlobal decls m
    -- Get all of the defs from imported modules (this is the env to check current module in)
    importedModules = filter (\x -> ModuleImport (moduleName x) `elem` moduleImports m') defs

-- | The Env-delta returned when type-checking a top-level Entry.
data HintOrCtx
  = AddHint TypeDecl
  | AddCtx [Entry]

-- | Check each sort of declaration in a module
tcEntry :: Entry -> TcMonad HintOrCtx
tcEntry (Def n term) = do
  oldDef <- Env.lookupDef n
  maybe tc die oldDef
  where
    tc = do
      lkup <- Env.lookupHint n
      case lkup of
        Nothing -> do
          ty <- inferType term
          return $ AddCtx [Decl (TypeDecl n ty), Def n term]
        Just decl ->
          let handler (Env.Err ps msg) = throwError $ Env.Err ps (msg $$ msg')
              msg' =
                disp
                  [ DS "When checking the term",
                    DD term,
                    DS "against the type",
                    DD decl
                  ]
           in do
                checkType term (declType decl) `catchError` handler
                return $ AddCtx [Decl decl, Def n term]
    die term' =
      Env.extendSourceLocation (unPosFlaky term) term $
        Env.err
          [ DS "Multiple definitions of",
            DD n,
            DS "Previous definition was",
            DD term'
          ]
tcEntry (Decl decl) = do
  duplicateTypeBindingCheck decl
  ensureType $ declType decl
  return $ AddHint decl
tcEntry (Data (TypeConstructor typ pack)) = do
  -- Unpacking
  (params, (arity, constructors)) <- Unbound.unbind pack
  let td = TypeDecl typ (telescopeToPi params arity)
  -- Typecheck the type definition
  ensureType (declType td)
  -- Check that we are defining the arity of a sort
  sort <- isArityOfSort arity
  -- Check that the name of that type is not already defined
  duplicateTypeBindingCheck td
  -- Check the constructors
  (cstrs, csts) <- unzip <$> Env.extendCtx (Decl td) (mapM (tcConstructor params (typ, sort)) constructors)
  -- Return env's extensions
  let cstDecls = Decl <$> csts
  return $ AddCtx (Data (TypeConstructor typ $ Unbound.bind params (arity, cstrs)) : Decl td : cstDecls)
tcEntry (Smaller _ _) = Env.err [DS "User defined smaller declarations are not allowed."]

tcConstructor :: Telescope -> (TName, Level) -> Constructor -> TcMonad (Constructor, TypeDecl)
tcConstructor typeTelescope (dataTypeName, sort) (Constructor name _ cstrType) = do
  -- Construct the type(s) of the constructor
  -- For
  -- ```
  -- data D (_ : T): U -> S := C0 (_ : A) : D I
  -- ```
  (cstrTelescope, rType) <- Unbound.unbind cstrType
  let -- Is A -> D I
      patternType = telescopeToPi cstrTelescope rType
      -- Is T -> A -> D I
      fullType = telescopeToPi typeTelescope patternType

  -- Ensure that the constructor is well-typed
  -- In particular, combined with the following check that it constructs the correct
  -- type, this ensures that the type is fully applied.
  ensureType fullType
      `catchError` const
        ( Env.err
            [ DD name,
              DS "has type",
              DD fullType,
              DS $ "which is not-well typed (is " ++ show dataTypeName ++ " fully applied?)"
            ]
        )

  -- Check that the constructor is for the datatype under consideration.
  (params, typeArgs) <-
    isConstructorOf fullType dataTypeName
      `catchError` const
        ( Env.err
            [ DD name,
              DS "has type",
              DD fullType,
              DS "but it should be constructor for",
              DD dataTypeName
            ]
        )

  -- Check that the type parameters are parametric
  let typeTeleLength = lengthTelescope typeTelescope
      typeParams = take typeTeleLength typeArgs
      varParams = Var . fst <$> params
  unless
    ( (typeTeleLength == length typeParams)
        && (typeTeleLength <= length params)
        && all (uncurry aeq) (zip varParams typeParams)
    )
    $ Env.err
      [ DS $ "The first " ++ (show . length) params ++ " argument(s) of the type of constructor",
        DD dataTypeName,
        DS "should be",
        DL $ DD <$> varParams,
        DS "found",
        DL $ DD <$> typeParams
      ]

  -- Check the positivity condition
  checkPositivity False dataTypeName fullType

  recComponents <- checkRecursiveComponents dataTypeName patternType

  -- TODO: add rec components
  return (Constructor name recComponents cstrType, TypeDecl name fullType)
  where
    checkPositivity :: Bool -> TName -> Term -> TcMonad ()
    checkPositivity strict v t = do
      t' <- Equal.whnf t
      case t' of
        (TyPi boundType bnd) -> do
          (_, r) <- Unbound.unbind bnd
          if strict
            then
              when (occursInTerm v boundType) $
                Env.err
                  [ DD v,
                    DS "is currently being defined, and hence is not allowed to appear on the left side of",
                    DD t'
                  ]
            else checkPositivity True v boundType
          checkPositivity strict v r
        _ | not $ occursInTerm v t' -> return ()
        _ -> do
          -- TODO: relax to allow uniform arguments to different datatype
          (_, args) <- catchError (Equal.unconstruct t') (\_ -> Env.err [DS ""])
          when (occursInArgs v args) $
            Env.err
              [ DD v,
                DS "is currently being defined, and hence is not allowed be used as an argument in",
                DD t'
              ]

    checkRecursiveComponents :: TName -> Type -> TcMonad [Bool]
    checkRecursiveComponents v t = do
      t' <- Equal.whnf t
      case t' of
        (TyPi boundType bnd) -> do
          (_, r) <- Unbound.unbind bnd
          (occursInTerm v boundType :) <$> checkRecursiveComponents v r
        _ -> return []

    occursInTerm :: TName -> Term -> Bool
    occursInTerm v' t =
      not $ null [v | v <- fv t, v == v']

    occursInArgs :: TName -> [Term] -> Bool
    occursInArgs v = any (occursInTerm v)

-- | Make sure that we don't have the same name twice in the
-- environment. (We don't rename top-level module definitions.)
duplicateTypeBindingCheck :: TypeDecl -> TcMonad ()
duplicateTypeBindingCheck decl = do
  -- Look for existing type bindings ...
  let n = declName decl
  l <- Env.lookupTyMaybe n
  l' <- Env.lookupHint n
  -- ... we don't care which, if either are Just.
  case catMaybes [l, l'] of
    [] -> return ()
    -- We already have a type in the environment so fail.
    decl' : _ ->
      let p = unPosFlaky $ declType decl
          msg =
            [ DS "Duplicate type declaration",
              DD decl,
              DS "Previous was",
              DD decl'
            ]
       in Env.extendSourceLocation p decl $ Env.err msg
