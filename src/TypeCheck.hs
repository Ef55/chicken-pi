{- pi-forall -}

{-# HLINT ignore "Use forM_" #-}
{-# HLINT ignore "Use lambda-case" #-}

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
subtype :: Type -> Type -> TcMonad ()
subtype (TyType l1) (TyType l2)
  | l1 == LProp || l1 == LSet = return () -- LProp and LSet are subtypes of any Type
  | l1 <= l2 = return () -- Universe cumulativity: l1 <= l2
  | otherwise = do
      gamma <- Env.getLocalCtx
      Env.err
        [ DS "Universe level mismatch: cannot use 'Type",
          DS (show l1),
          DS "' where 'Type",
          DS (show l2),
          DS "' is expected.",
          DS "In context:",
          DD gamma
        ]
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
      let l = case (l1, l2) of
           (_, LProp) -> LProp
           (_, LSet) -> LSet
           (LConst i, LConst j) -> LConst (max i j)
           (LProp, l) -> l
           (LSet, l) -> l
      return (TyType l) -- Pi types are in universe level 'l'


  -- i-app
  (App a b) -> do
    ty1 <- inferType a
    ty1' <- Equal.whnf ty1
    case ty1' of
      (TyPi tyA bnd) -> do
        checkType b tyA
        return (instantiate bnd b)
      _ -> Env.err [DS "Expected a function type but found", DD a, DS "of type", DD ty1]

  -- i-ann
  (Ann a tyA) -> do
    u <- tcType tyA
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
    [] -> True  -- Empty type
    [_] -> True -- Singleton type
    _ -> False  -- More than one constructor

checkCase :: Term -> DestructionPredicate -> [Branch] -> Maybe Type -> TcMonad Type
checkCase scrut pred branches mRet = do
  (typeDecl, typeParams, pred, ret) <- checkScrutinee scrut pred mRet
  checkMatch pred typeDecl typeParams branches
  return ret

instantiateDestructionPredicate :: Term -> [Type] -> Unbound.Bind (TName, Pattern) Type -> TcMonad Type
instantiateDestructionPredicate scrut typeArgs pred = do
  ((sVar, PatCon _ typeArgVars), res) <- Unbound.unbind pred
  scrutType <- inferType scrut
  scrutType' <- Equal.whnf scrutType
  case scrutType' of
    TyType _ -> do
      -- If scrutinee is a sort, destruct into a function
      let newRes = TyPi scrutType (Unbound.bind sVar res)
      return $ Unbound.substs ((sVar, scrut) : zip typeArgVars typeArgs) newRes
    _ -> do
      -- Original case for non-sort types
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
  sType' <- Equal.whnf sType
  case sType' of
    TyPi tyA bnd -> do
      -- Handle dependent destruction: apply destruction under the binder
      (x, bodyType) <- Unbound.unbind bnd
      (typeDecl, typeParams, pred, ret) <- checkScrutinee (App s (Var x)) p mExp
      return (typeDecl, typeParams, pred, TyPi tyA (Unbound.bind x ret))

    TySigma tyA bnd -> do
      (x, bodyType) <- Unbound.unbind bnd
      (typeDecl, typeParams, pred, ret) <- checkScrutinee (App s (Var x)) p mExp
      return (typeDecl, typeParams, pred, TySigma tyA (Unbound.bind x ret))

    TyType LProp -> do
      -- First, try to unconstruct sType to see if it actually represents a datatype
      case Equal.maybeUnconstruct sType of
        Nothing ->
          -- If we can't unconstruct it, it's just a bare Prop, not a datatype
          Env.err [DS "Cannot eliminate bare `Prop` sort, it's not a datatype."]
        Just (typeCstrName, typeArgs) -> do
          tcLookup <- Env.lookupTypeConstructor typeCstrName
          case tcLookup of
            Just typeDecl -> do
              -- Check if it's empty or singleton
              isSpecial <- isEmptyOrSingleton typeDecl
              if isSpecial
                then do
                  -- Allow elimination into any sort
                  let newRet = fromMaybe (TyType LSet) mExp
                  -- Transform `bPred` into a fully-specified predicate
                  ((maybeAsBind, maybeInBind), maybeRet) <- Unbound.unbind bPred
                  asBind <- maybe Env.freshWildcard return maybeAsBind
                  inBind <- maybe (generatePattern typeCstrName typeArgs) return maybeInBind
                  ret <- case (maybeRet, mExp) of
                    (Just ret, _) -> return ret
                    (_, Just ret) -> return ret
                    (Nothing, Nothing) ->
                      Env.err
                        [ DS "Cannot infer return type of case expression",
                          DD dummy
                        ]

                  let pred = Unbound.bind (asBind, inBind) ret
                  return (typeDecl, typeArgs, pred, newRet)
                else
                  Env.err
                    [ DS "Cannot eliminate",
                      DD sType,
                      DS "into a non-Prop sort unless it is empty or singleton."
                    ]
            Nothing -> Env.err [DS "Could not find type constructor for", DD typeCstrName]

    _ -> do
      -- Handle non-dependent and non-Prop cases
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
    generatePattern typeCstrName typeArgs =
      PatCon (Unbound.name2String typeCstrName) <$> mapM (const Env.freshWildcard) typeArgs

    splitParamsIndices :: TypeConstructor -> [Type] -> TcMonad ([Type], [Type])
    splitParamsIndices (TypeConstructor _ pack) args = do
      (telescope, _) <- Unbound.unbind pack
      let params :: [TName] = Unbound.toListOf Unbound.fv telescope
          paramCount = length params
      return $ splitAt paramCount args


checkMatch :: Unbound.Bind (TName, Pattern) Type -> TypeConstructor -> [Type] -> [Branch] -> TcMonad ()
checkMatch ret (TypeConstructor typeName pack) typeParams branches = do
  (_, (_, constructors)) <- instantiateTelescope pack typeParams

  when (length branches /= length constructors) $
    Env.err
      [ DS $ "Pattern matching has " ++ show (length branches) ++ " branches, yet the matched type",
        DD typeName,
        DS $ "has " ++ show (length constructors) ++ " constructors."
      ]
  mapM_ (uncurry (checkBranch ret typeParams)) (zip constructors branches)

checkBranch :: Unbound.Bind (TName, Pattern) Type -> [Type] -> Constructor -> Branch -> TcMonad ()
checkBranch retPred typeParams cstr@(Constructor cstrName cstrType) (Branch branch) = do
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
      scrut = foldl App (Var cstrName) cstrArgs
  typeArgs <- Equal.instantiateConstructorType cstrName cstrArgs
  ret <- instantiateDestructionPredicate scrut typeArgs retPred

  -- Retrieve the type of the bindings in the telescope
  (telescope, _) <- instantiateTelescope cstrType cstrVars
  let entries = zipWith (\x t -> Decl $ TypeDecl x t) xs telescope

  when (length telescope /= length xs) $
    Env.err
      [ DS "Pattern",
        DD pat,
        DS "does not bind the correct number of variables for constructor",
        DD cstr
      ]

  Env.extendCtxs entries $ do
    -- Infer the type of the body
    bodyType <- inferType body
    -- Enforce that the body type matches the expected type
    Equal.equate bodyType ret
    -- Continue to type check the body against ret
    checkType body ret

-------------------------------------------------------------------------

-- | Make sure that the term is a "type" (i.e. that it has type 'Type')
tcType :: Term -> TcMonad Level
tcType tm = do
  ty <- inferType tm
  ty' <- Equal.whnf ty
  case ty' of
    TyType LProp -> return LProp
    TyType LSet -> return LSet
    TyType (LConst i) -> return (LConst i)
    _ -> Env.err [DS "Expected", DD tm, DS "to have type 'Type l' for some level l, but found", DD ty']

-- | Make sure that the term is a sort
isSort :: Term -> TcMonad Term
isSort tm = do
  tm' <- Equal.whnf tm
  case tm' of
    TyType _ -> return tm'
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

isArityOfSort :: Type -> TcMonad Term
isArityOfSort t = do
  (_, t') <- arityOf t
  isSort t'

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
        l1 <- tcType tyA
        Env.extendCtx (Decl (TypeDecl x tyA)) $ do
          l2 <- tcType tyB 
          let l = case (l1, l2) of
                (_, LProp) -> LProp
                (_, LSet) -> LSet
                (LConst i, LConst j) -> LConst (max i j)
                (LProp, l) -> l
                (LSet, l) -> l
          -- Ensure that l <= tyPiLevel (universe cumulativity)
          tyPiLevel <- tcType ty'
          unless (l <= tyPiLevel) $
            Env.err
              [ DS "Expected",
                DD ty',
                DS "but found a function type in universe level",
                DS (show l)
              ]
          -- Check the body
          checkType body tyB
        return ()
      _ -> Env.err [DS "Lambda expression should have a function type, not", DD ty']
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
          l1 <- tcType tyA
          checkType a tyA
          Env.extendCtxs [mkDecl x tyA, Def x a] $ do
            l2 <- tcType tyB
            let l = case (l1, l2) of
                 (_, LProp) -> LProp
                 (_, LSet) -> LSet
                 (LConst i, LConst j) -> LConst (max i j)
                 (LProp, l) -> l
                 (LSet, l) -> l
            -- Ensure that l <= tySigmaLevel (universe cumulativity)
            tySigmaLevel <- tcType ty'
            unless (l <= tySigmaLevel) $
              Env.err
                [ DS "Expected",
                  DD ty',
                  DS "but found a Sigma type in universe level",
                  DS (show l)
                ]
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
          l1 <- tcType tyA
          let tyB = instantiate bnd' (Var x)
          l2 <- Env.extendCtx (mkDecl x tyA) $ tcType tyB
          decl <- Equal.unify [] p (Prod (Var x) (Var y))
          Env.extendCtxs ([mkDecl x tyA, mkDecl y tyB] ++ decl) $
            checkType body ty'
        _ -> Env.err [DS "Scrutinee of LetPair must have Sigma type"]
    -- c-let
    (Let a bnd) -> do
      (x, b) <- unbind bnd
      tyA <- inferType a
      l <- tcType tyA
      Env.extendCtxs [mkDecl x tyA, Def x a] $
        checkType b ty'
    -- c-refl
    Refl -> case ty' of
      (TyEq a b) -> Equal.equate a b
      _ -> Env.err [DS "Refl annotated with invalid type", DD ty']
    -- c-subst
    (Subst a b) -> do
      tp <- inferType b
      l_tp <- tcType tp
      nf <- Equal.whnf tp
      (m, n) <- case nf of
        TyEq m n -> return (m, n)
        _ -> Env.err [DS "Subst requires an equality type, not", DD tp]
      _ <- inferType m >>= tcType
      _ <- inferType n >>= tcType
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
      _ <- inferType a >>= tcType
      _ <- inferType b >>= tcType
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
      subtype tyA ty' -- Use subtype to handle universe cumulativity

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
                Env.extendCtx (Decl decl) $ checkType term (declType decl) `catchError` handler
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
  u <- tcType (declType decl)
  return $ AddHint decl
tcEntry dat@(Data (TypeConstructor typ pack)) = do
  -- Unpacking
  (params, (arity, constructors)) <- Unbound.unbind pack
  let td = TypeDecl typ (telescopeToPi params arity)

  -- Typecheck the type definition
  _ <- tcType (declType td)
  -- Check that we are defining the arity of a sort
  sort <- isArityOfSort arity
  -- Check that the name of that type is not already defined
  duplicateTypeBindingCheck td

  cstrs <- Env.extendCtx (Decl td) $ mapM (tcConstructor params (typ, sort)) constructors
  let decls = Decl <$> cstrs
  return $ AddCtx (dat : Decl td : decls)

tcConstructor :: Telescope -> (TName, Type) -> Constructor -> TcMonad TypeDecl
tcConstructor typeTelescope (dataTypeName, sort) (Constructor name cstrType) = do
  -- Construct the type of the constructor as a constant of the language
  (cstrTelescope, rType) <- Unbound.unbind cstrType
  let fullType = telescopeToPi typeTelescope $ telescopeToPi cstrTelescope rType

  -- Ensure that the constructor generates the correct sort
  -- In particular, combined with the following check that it constructs the correct
  -- type, this ensures that the type is fully applied.
  checkType fullType sort
    `catchError` const
      ( Env.err
          [ DD fullType,
            DS "should have type",
            DD sort,
            DS "which is the sort of its constructor (is it fully applied?)."
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

  return $ TypeDecl name fullType
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
