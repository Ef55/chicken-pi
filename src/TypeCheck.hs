{- pi-forall -}

{-# HLINT ignore "Use forM_" #-}

-- | The main routines for type-checking
module TypeCheck (tcModules, inferType, checkType) where

import Control.Monad.Except
import Data.Maybe (catMaybes)
import Debug.Trace
import Environment (D (..), TcMonad)
import Environment qualified as Env
import Equal qualified
import PrettyPrint (Disp (disp), pp, debug, D(..))
import Syntax
import Text.PrettyPrint.HughesPJ (render, ($$))
import Unbound.Generics.LocallyNameless (string2Name)
import Unbound.Generics.LocallyNameless qualified as Unbound

---------------------------------------------------------------------
-- Helper function for implementing impredicativity
imax :: Level -> Level -> Level
imax l1 (LConst 0) = LConst 0
imax l1 l2 = LMax l1 l2

subtype :: Type -> Type -> TcMonad ()
subtype (TyType l1) (TyType l2) = Equal.equateLevels l1 l2
subtype ty1 ty2 = Equal.equate ty1 ty2

-- | Infer/synthesize the type of a term
inferType :: Term -> TcMonad Type
inferType a = case a of
  -- i-var
  (Var x) -> do
    decl <- Env.lookupTy x -- make sure the variable is accessible
    Env.checkStage (declEp decl)
    return (declType decl)

  -- i-type
  TyType l -> return (TyType (LPlus l 1))  -- Type l : Type (l + 1)

  -- i-pi
  (TyPi ep tyA bnd) -> do
    (x, tyB) <- unbind bnd
    l1 <- tcType tyA
    Env.extendCtx (Decl (TypeDecl x ep tyA)) $ do
      l2 <- tcType tyB
      let l = imax l1 l2
      return (TyType l)  -- Pi types are in the universe level 'l'

  -- i-app
  (App a b) -> do
    ty1 <- inferType a 
    ty1' <- Equal.whnf ty1 
    case ty1' of 
      (TyPi ep1 tyA bnd) -> do
          unless (ep1 == argEp b) $ Env.err 
            [DS "In application, expected", DD ep1, DS "argument but found", 
                                            DD b, DS "instead." ]
          -- If the argument is Irrelevant, adjust the context
          (if ep1 == Irr then Env.extendCtx (Demote Rel) else id) $ checkType (unArg b) tyA 
          return (instantiate bnd (unArg b) )
      _ -> Env.err [DS "Expected a function type but found ", DD ty1]

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
      let l = imax l1 l2
      return (TyType l)  -- Sigma types are in universe level 'l'

  -- i-eq
  (TyEq a b) -> do
    aTy <- inferType a
    checkType b aTy
    return Prop -- Equality types are in Prop (Type 0)

  (Case scrut (Just ret) branches) -> do
    checkMatch scrut ret branches
    return ret
  (Case _ Nothing _) ->
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
checkMatch :: Term -> Type -> [Branch] -> TcMonad ()
checkMatch scrut ret branches = do
  tyS <- inferType scrut
  ret <- Equal.whnf ret
  (TypeDecl typeName _ _, constructors) <- checkTypeConstructor tyS
  when (length branches /= length constructors) $
    Env.err
      [ DS $ "Pattern matching has " ++ show (length branches) ++ " branches, yet the matched type",
        DD typeName,
        DS $ "has " ++ show (length constructors) ++ " constructors."
      ]
  let branchesCheck = zip constructors branches
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
        -- If we are matching a variable, we can inject its definition in term
        -- of the pattern it matches in the context.
        let decl = case scrut of
              Var s -> [Def s (foldl App (Var expCstr) (Arg Rel . Var <$> xs))]
              _ -> []
        Env.extendCtxs decl $
          enterBranch xs tele $
            checkType body ret
    )
    branchesCheck
  where
    checkTypeConstructor :: Type -> TcMonad (TypeDecl, [Constructor])
    checkTypeConstructor tyS =
      Equal.unconstruct tyS
        >>= \(m, _) -> do
          m' <- Env.lookupTypeConstructor m
          case m' of
            Nothing -> Env.err [DD m, DS "is not a type constructor"]
            Just d -> return d

    enterBranch :: [TName] -> Telescope -> TcMonad a -> TcMonad a
    enterBranch names tele k = do
      case (names, tele) of
        (n : ns, Tele t) -> do
          let ((x, Unbound.Embed xType), t') = Unbound.unrebind t
              t'' = Unbound.subst x (Var n) t'
          Env.extendCtx (Decl $ TypeDecl n Rel xType) $ enterBranch ns t'' k
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
        (_, _) -> k


-------------------------------------------------------------------------

-- | Make sure that the term is a "type" (i.e. that it has type 'Type')
tcType :: Term -> TcMonad Level
tcType tm = Env.withStage Irr $ do
  ty <- inferType tm
  ty' <- Equal.whnf ty
  case ty' of
    TyType l -> return l
    _ -> Env.err [DS "Expected", DD tm, DS "to have type 'Type l' for some level l, but found", DD ty']

-------------------------------------------------------------------------

-- | Check that the given term has the expected type
-- | Check that the given term has the expected type
checkType :: Term -> Type -> TcMonad ()
checkType tm ty = do
  ty' <- Equal.whnf ty
  case tm of
    -- c-lam: check the type of a function
    (Lam ep1 bnd) -> case ty' of
      (TyPi ep2 tyA bnd2) -> do
        -- unbind variables and check the body
        (x, body, tyB) <- unbind2 bnd bnd2
        -- check that ep1 == ep2
        unless (ep1 == ep2) $ Env.err [DS "In function definition, expected", DD ep2, DS "parameter", DD x, 
                                      DS "but found", DD ep1, DS "instead."]
        l1 <- tcType tyA
        Env.extendCtx (Decl (TypeDecl x ep1 tyA)) $ do
          l2 <- tcType tyB
          let l = imax l1 l2
          -- Ensure that l <= tyPiLevel (universe cumulativity)
          tyPiLevel <- tcType ty'
          unless (l <= tyPiLevel) $
            Env.err [DS "Expected", DD ty',
                     DS "but found a function type in universe level", DS (show l)]
          -- Check the body
          checkType body tyB
        return ()
      _ -> Env.err [DS "Lambda expression should have a function type, not", DD ty']
    -- Practicalities
    (Pos p a) ->
      Env.extendSourceLocation p a $ checkType a ty'
    TrustMe -> return ()
    PrintMe -> do
      gamma <- Env.getLocalCtx
      Env.warn [DS "Unmet obligation.\nContext:", DD gamma,
            DS "\nGoal:", DD ty']
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
            let l = imax l1 l2
            -- Ensure that l <= tySigmaLevel (universe cumulativity)
            tySigmaLevel <- tcType ty'
            unless (l <= tySigmaLevel) $
              Env.err [DS "Expected", DD ty',
                       DS "but found a Sigma type in universe level", DS (show l)]
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
          let l = imax l1 l2
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
                  TyEq m n -> return (m,n)
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
                  TyEq m n -> return (m,n)
                  _ -> Env.err [DS "Contra requires an equality type, not", DD ty_p]
      _ <- inferType a >>= tcType
      _ <- inferType b >>= tcType
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

    -- We only check the type if the pattern matching has no return clause.
    -- Otherwise, we can just le it be handled by inferType.
    (Case scrut Nothing branches) -> checkMatch scrut ty' branches
    -- c-infer
    _ -> do
      tyA <- inferType tm
      Equal.equate tyA ty'  -- Use Equal.equate to handle universe cumulativity


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
  u <- tcType (declType decl)
  return $ AddHint decl
tcEntry (Demote ep) = return (AddCtx [Demote ep])
tcEntry dat@(Data typ constructors) = do
  duplicateTypeBindingCheck typ
  cstrs <- Env.extendCtx dat $ tcConstructors constructors
  return $ AddCtx (dat : cstrs)
  where
    tcConstructors :: [Constructor] -> TcMonad [Entry]
    tcConstructors [] = return []
    tcConstructors (h : t) = do
      h' <- tcConstructor typ h
      t' <- tcConstructors t
      return (Decl h' : t')

tcConstructor :: TypeDecl -> Constructor -> TcMonad TypeDecl
tcConstructor dat@(TypeDecl dataTypeName _ _) (Constructor name cstrType) = do
  -- TODO: positivity check
  (tele, r) <- Unbound.unbind cstrType
  typ <- checkTelescope tele $ checkConstructor r
  return $ TypeDecl name Rel typ
  where
    checkConstructor :: Type -> TcMonad Type
    checkConstructor t = do
      (name, args) <- Equal.unconstruct t
      -- TODO: type indices/parameters
      guard (null args)
      -- which must by the type being defined.
      if name == dataTypeName
        then return $ foldl App (Var name) (Arg Rel <$> args)
        else
          Env.err
            [ DS "The constructor",
              DD name,
              DS "should be for type",
              DD dataTypeName,
              DS ", ",
              DD name,
              DS "found instead"
            ]

    checkTelescope :: Telescope -> TcMonad Type -> TcMonad Type
    checkTelescope Empty k = k
    checkTelescope (Tele bnd) k = do
      let ((x, Unbound.Embed xType), t') = Unbound.unrebind bnd
      t <- Env.extendCtxs [mkDecl x xType] $ checkTelescope t' k
      return $ TyPi Rel xType (Unbound.bind x t)

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
