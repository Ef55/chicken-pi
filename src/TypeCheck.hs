{- pi-forall -}

{-# HLINT ignore "Use forM_" #-}

-- | The main routines for type-checking
module TypeCheck (tcModules, inferType, checkType) where

import Control.Monad.Except
import Data.Maybe (catMaybes, fromMaybe)
import Debug.Trace
import Environment (D (..), TcMonad)
import Environment qualified as Env
import Equal qualified
import PrettyPrint (Disp (disp))
import Syntax
import Text.PrettyPrint.HughesPJ (render, ($$))
import Unbound.Generics.LocallyNameless (string2Name)
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold qualified as Unbound
import Unbound.Generics.LocallyNameless.Unsafe qualified as Unbound

---------------------------------------------------------------------

-- | Infer/synthesize the type of a term
inferType :: Term -> TcMonad Type
inferType a = case a of
  -- i-var
  (Var x) -> do
    decl <- Env.lookupTy x -- make sure the variable is accessible
    Env.checkStage (declEp decl)
    return (declType decl)

  -- i-type
  TyType -> return TyType
  -- i-pi
  (TyPi ep tyA bnd) -> do
    (x, tyB) <- unbind bnd
    tcType tyA
    Env.extendCtx (Decl (TypeDecl x ep tyA)) (tcType tyB)
    return TyType

  -- i-app
  (App a b) -> do
    ty1 <- inferType a
    ty1' <- Equal.whnf ty1
    case ty1' of
      (TyPi {- SOLN EP -} ep1 {- STUBWITH -} tyA bnd) -> do
        unless (ep1 == argEp b) $
          Env.err
            [ DS "In application, expected",
              DD ep1,
              DS "argument but found",
              DD b,
              DS "instead."
            ]
        -- if the argument is Irrelevant, resurrect the context
        (if ep1 == Irr then Env.extendCtx (Demote Rel) else id) $ checkType (unArg b) tyA
        return (instantiate bnd (unArg b))
      _ -> Env.err [DS "Expected a function type but found", DD a, DS "of type", DD ty1]

  -- i-ann
  (Ann a tyA) -> do
    tcType tyA
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
    tcType tyA
    Env.extendCtx (mkDecl x tyA) $ tcType tyB
    return TyType
  -- i-eq
  (TyEq a b) -> do
    aTy <- inferType a
    checkType b aTy
    return TyType
  (Case scrut branches) -> do
    (inPattern, (ret, branches)) <- Unbound.unbind branches
    case ret of
      Just ret -> checkMatch scrut ret Nothing inPattern branches >> return ret
      Nothing ->
        Env.err
          [ DS "In",
            DD a,
            DS "cannot infer typ of pattern matching without `return` clause"
          ]
  -- cannot synthesize the type of the term
  _ ->
    Env.err [DS "Must have a type annotation for", DD a]

-------------------------------------------------------------------------

-- | Typecheck a pattern-matching construct
checkMatch :: Term -> Type -> Maybe Type -> Maybe Pattern -> [Branch] -> TcMonad ()
checkMatch scrut ret retComp inPattern branches = do
  tyS <- inferType scrut
  ret <- Equal.whnf ret
  (typeName, typeArgs, pack) <- checkTypeConstructor tyS
  (paramsBinders, constructors) <- Unbound.unbind pack
  (constructors, indices) <- substTele typeArgs paramsBinders constructors
  let params = take (length typeArgs - length indices) typeArgs
  when (length branches /= length constructors) $
    Env.err
      [ DS $ "Pattern matching has " ++ show (length branches) ++ " branches, yet the matched type",
        DD typeName,
        DS $ "has " ++ show (length constructors) ++ " constructors."
      ]
  case (retComp, inPattern) of
    (Nothing, _) -> return ()
    (Just retComp, Nothing) -> Equal.equate ret retComp
    (Just retComp, Just (PatCon _ inVars)) -> do
      Env.extendCtxs (zipWith Def inVars typeArgs) $ Equal.equate ret retComp
  mapM_
    ( \(Constructor expCstr typCstr, branch) -> do
        (PatCon cstr xs, body) <- Unbound.unbind (getBranch branch)
        when (expCstr /= string2Name cstr) $
          Env.err
            [ DS "Pattern is headed by",
              DD cstr,
              DS "but constructor",
              DD expCstr,
              DS "was expected."
            ]
        (tele, _) <- Unbound.unbind typCstr

        let cstrArgs = params ++ (Var <$> xs)
            decl = case scrut of
              Var s -> [Def s (foldl App (Var expCstr) (Arg Rel <$> cstrArgs))]
              _ -> []
        cstrIndicies <- Equal.instantiateConstructorType expCstr cstrArgs
        typeArgDecls <- case inPattern of
          Nothing -> return []
          Just (PatCon _ inPattern) ->
            return $ zipWith Def inPattern cstrIndicies
        enterBranch xs tele $ \_ ->
          Env.extendCtxs (decl ++ typeArgDecls) $
            checkType body ret
    )
    (zip constructors branches)
  where
    checkTypeConstructor :: Type -> TcMonad (TName, [Term], Unbound.Bind Telescope [Constructor])
    checkTypeConstructor tyS =
      Equal.unconstruct tyS
        >>= \(m, params) -> do
          m' <- Env.lookupTypeConstructor m
          case m' of
            Nothing -> Env.err [DD m, DS "is not a type constructor"]
            Just (TypeConstructor name _ cstrs) -> return (name, params, cstrs)

    substTele :: [Term] -> Telescope -> [Constructor] -> TcMonad ([Constructor], [Term])
    substTele as Empty r = return (r, as)
    substTele (a : as) (Tele t) r = do
      let ((x, _), t') = Unbound.unrebind t
          t'' = Unbound.subst x a t'
          r' = Unbound.subst x a r
      substTele as t'' r'
    substTele _ _ _ = error "Internal error: substTele failed"

    enterBranch :: [TName] -> Telescope -> ([TName] -> TcMonad a) -> TcMonad a
    enterBranch = iter []
      where
        iter :: [TName] -> [TName] -> Telescope -> ([TName] -> TcMonad a) -> TcMonad a
        iter vars names tele k = do
          case (names, tele) of
            (n : ns, Tele t) -> do
              let ((x, Unbound.Embed xType), t') = Unbound.unrebind t
                  t'' = Unbound.subst x (Var n) t'
              Env.extendCtx (Decl $ TypeDecl n Rel xType) $ iter (x : vars) ns t'' k
            -- The following errors currently cannot occur due to the instantiation
            -- of the constructor prior to trying to enter the branch.
            ([], t@(Tele _)) ->
              Env.err
                [ DS "Too few variables in pattern: parameters",
                  DD t,
                  DS "are not bound."
                ]
            (n : _, _) ->
              Env.err
                [ DS "Too many variables in pattern:",
                  DD n,
                  DS "is the first unused name."
                ]
            (_, _) -> k vars

-------------------------------------------------------------------------

-- | Make sure that the term is a "type" (i.e. that it has type 'Type')
tcType :: Term -> TcMonad ()
tcType tm = Env.withStage Irr $ checkType tm TyType

-- | Make sure that the term is a sort
isSort :: Term -> TcMonad Term
isSort tm
  | aeq tm TyType = return TyType
  | otherwise = Env.err [DD tm, DS "is not a sort."]

arityOf :: Type -> (Type -> TcMonad a) -> TcMonad a
arityOf t k =
  Equal.whnf t >>= \t' -> case t' of
    TyPi rel xType bnd -> do
      (x, body) <- Unbound.unbind bnd
      Env.extendCtx (Decl $ TypeDecl x rel xType) $ arityOf body k
    _ -> k t

isArityOfSort :: Type -> TcMonad Term
isArityOfSort t = arityOf t isSort

isConstructorOf :: Type -> TName -> TcMonad [Term]
isConstructorOf t typ = do
  (h, args) <- Equal.unconstruct t
  unless (h == typ) $ Env.err [DS "The constructor has type", DD t, DS "expected a constructor for", DD typ]
  return args

-------------------------------------------------------------------------

-- | Check that the given term has the expected type
checkType :: Term -> Type -> TcMonad ()
checkType tm ty = do
  ty' <- Equal.whnf ty
  case tm of
    -- c-lam: check the type of a function
    (Lam ep1 bnd) -> case ty' of
      (TyPi ep2 tyA bnd2) -> do
        -- unbind the variables in the lambda expression and pi type
        (x, body, tyB) <- unbind2 bnd bnd2
        -- epsilons should match up
        unless (ep1 == ep2) $
          Env.err
            [ DS "In function definition, expected",
              DD ep2,
              DS "parameter",
              DD x,
              DS "but found",
              DD ep1,
              DS "instead."
            ]
        -- check the type of the body of the lambda expression
        Env.extendCtx (Decl (TypeDecl x ep1 tyA)) (checkType body tyB)
      _ -> Env.err [DS "Lambda expression should have a function type, not", DD ty']
    -- Practicalities
    (Pos p a) ->
      Env.extendSourceLocation p a $ checkType a ty'
    TrustMe -> Env.warn [ DS "Unmet obligation." ]
    PrintMe -> do
      gamma <- Env.getLocalCtx
      Env.warn
        [ DS "Unmet obligation.\nContext:",
          DD gamma,
          DS "\nGoal:",
          DD ty'
        ]

    -- c-prod
    (Prod a b) -> do
      case ty' of
        (TySigma tyA bnd) -> do
          (x, tyB) <- unbind bnd
          checkType a tyA
          Env.extendCtxs [mkDecl x tyA, Def x a] $ checkType b tyB
        _ ->
          Env.err
            [ DS "Products must have Sigma Type",
              DD ty,
              DS "found instead"
            ]

    -- c-letpair
    (LetPair p bnd) -> do
      ((x, y), body) <- Unbound.unbind bnd
      pty <- inferType p
      pty' <- Equal.whnf pty
      case pty' of
        TySigma tyA bnd' -> do
          let tyB = instantiate bnd' (Var x)
          decl <- Equal.unify [] p (Prod (Var x) (Var y))
          Env.extendCtxs ([mkDecl x tyA, mkDecl y tyB] ++ decl) $
            checkType body ty'
        _ -> Env.err [DS "Scrutinee of LetPair must have Sigma type"]

    -- c-let
    (Let a bnd) -> do
      (x, b) <- unbind bnd
      tyA <- inferType a
      Env.extendCtxs [mkDecl x tyA, Def x a] $
        checkType b ty'
    -- c-refl
    Refl -> case ty' of
      (TyEq a b) -> Equal.equate a b
      _ -> Env.err [DS "Refl annotated with invalid type", DD ty']
    -- c-subst
    (Subst a b) -> do
      -- infer the type of the proof 'b'
      tp <- inferType b
      -- make sure that it is an equality between m and n
      nf <- Equal.whnf tp
      (m, n) <- case nf of
        TyEq m n -> return (m, n)
        _ -> Env.err [DS "Subst requires an equality type, not", DD tp]
      -- if either side is a variable, add a definition to the context
      edecl <- Equal.unify [] m n
      -- if proof is a variable, add a definition to the context
      pdecl <- Equal.unify [] b Refl
      Env.extendCtxs (edecl ++ pdecl) $ checkType a ty'
    -- c-contra
    (Contra p) -> do
      ty' <- inferType p
      nf <- Equal.whnf ty'
      (a, b) <- case nf of
        TyEq m n -> return (m, n)
        _ -> Env.err [DS "Contra requires an equality type, not", DD ty']
      a' <- Equal.whnf a
      b' <- Equal.whnf b
      -- TODO: extend to datatypes
      case (a', b') of
        (_, _) ->
          Env.err
            [ DS "I can't tell that",
              DD a,
              DS "and",
              DD b,
              DS "are contradictory"
            ]
    (Case scrut branches) -> do
      (inPattern, (ret, branches)) <- Unbound.unbind branches
      let tyR = fromMaybe ty' ret
      checkMatch scrut tyR (Just ty') inPattern branches
    -- c-infer
    _ -> do
      tyA <- inferType tm
      Equal.equate tyA ty'

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

teleToPi :: Telescope -> Type -> Type
teleToPi t r = iter t
  where
    iter :: Telescope -> Type
    iter Empty = r
    iter (Tele bnd) = do
      let ((x, Unbound.Embed xType), t') = Unbound.unrebind bnd
          b = iter t'
       in TyPi Rel xType (Unbound.bind x b)

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
          return $ AddCtx [Decl (TypeDecl n Rel ty), Def n term]
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
  tcType (declType decl)
  return $ AddHint decl
tcEntry (Demote ep) = return (AddCtx [Demote ep])
tcEntry dat@(Data (TypeConstructor typ arity pack)) = do
  sort <- isArityOfSort arity
  (params, constructors) <- Unbound.unbind pack
  let td = TypeDecl typ Rel (teleToPi params arity)
  duplicateTypeBindingCheck td
  cstrs <- Env.extendCtx (Decl td) $ underTelescope params $ \p -> tcConstructors (typ, sort) p constructors
  return $ AddCtx (dat : Decl td : cstrs)
  where
    underTelescope :: Telescope -> ([(TName, Type)] -> TcMonad a) -> TcMonad a
    underTelescope t k = iter [] t
      where
        iter p Empty = k (reverse p)
        iter p (Tele bnd) = do
          let ((x, Unbound.Embed xType), t') = Unbound.unrebind bnd
          Env.extendCtxs [mkDecl x xType] $ iter ((x, xType) : p) t'

    tcConstructors :: (TName, Type) -> [(TName, Type)] -> [Constructor] -> TcMonad [Entry]
    tcConstructors _ _ [] = return []
    tcConstructors typ params (h : t) = do
      h' <- tcConstructor typ params h
      t' <- tcConstructors typ params t
      return (Decl h' : t')

tcConstructor :: (TName, Type) -> [(TName, Type)] -> Constructor -> TcMonad TypeDecl
tcConstructor (dataTypeName, sort) params (Constructor name cstrType) = do
  (tele, r) <- Unbound.unbind cstrType
  typ <- checkTelescope tele $ checkConstructor r
  let typ' = foldr (\(b, bT) t -> TyPi Rel bT $ Unbound.bind b t) typ params
  return $ TypeDecl name Rel typ'
  where
    checkConstructor :: Type -> TcMonad Type
    checkConstructor t = do
      -- Check that the constructor is for the datatype under consideration
      args <-
        isConstructorOf t dataTypeName
          `catchError` const
            ( Env.err
                [ DD name,
                  DS "has type",
                  DD t,
                  DS "but it should be constructor for",
                  DD dataTypeName
                ]
            )
      -- Check that it type checks AND is fully applied
      checkType t sort
        `catchError` const
          ( Env.err
              [ DD t,
                DS "should have type",
                DD sort,
                DS "which is the sort of its constructor (is it fully applied?)."
              ]
          )
      -- Check that the parameters are instantiated to themselves
      unless ((length params <= length args) && all (uncurry aeq) (zip (Var . fst <$> params) (take (length params) args))) $
        Env.err
          [ DS $ "The first " ++ (show . length) params ++ " argument(s) of the type of constructor",
            DD name,
            DS "should be",
            DL $ DD . fst <$> params,
            DS "found",
            DL $ DD <$> args
          ]
      -- Check for strict positivity
      -- TODO: relax for uniform parameters
      when (occursInArgs dataTypeName args) $
        Env.err
          [ DD dataTypeName,
            DS "is currently being defined, and hence is not allowed to be used as an argument in",
            DD t
          ]
      return $ foldl App (Var dataTypeName) (Arg Rel <$> args)

    checkTelescope :: Telescope -> TcMonad Type -> TcMonad Type
    checkTelescope Empty k = k
    checkTelescope (Tele bnd) k = do
      let ((x, Unbound.Embed xType), t') = Unbound.unrebind bnd
      checkStrictPositivity dataTypeName xType
      t <- Env.extendCtxs [mkDecl x xType] $ checkTelescope t' k
      return $ TyPi Rel xType (Unbound.bind x t)

    checkStrictPositivity :: TName -> Term -> TcMonad ()
    checkStrictPositivity v t = do
      t' <- Equal.whnf t
      case t' of
        (TyPi _ boundType bnd) -> do
          (_, r) <- Unbound.unbind bnd
          when (occursInTerm v boundType) $
            Env.err
              [ DD v,
                DS "is currently being defined, and hence is not allowed to appear on the left side of",
                DD t'
              ]
          checkStrictPositivity v r
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
