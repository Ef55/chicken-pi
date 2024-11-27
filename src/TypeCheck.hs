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
import PrettyPrint (Disp (disp), debug, pp)
import Syntax
import Text.PrettyPrint.HughesPJ (render, ($$))
import Unbound.Generics.LocallyNameless (string2Name)
import Unbound.Generics.LocallyNameless qualified as Unbound

splitAppliedConstructor :: Term -> TcMonad (TName, [Term])
splitAppliedConstructor term = iter term []
  where
    iter :: Term -> [Term] -> TcMonad (TName, [Term])
    iter term acc = case term of
      App l (Arg _ r) -> iter l (r : acc)
      (Var name) -> return (name, acc)
      _ ->
        Env.err
          [ DS "Expected constructor at head",
            DD term,
            DS "is not headed by a constructor."
          ]

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
      _ -> Env.err [DS "Expected a function type but found ", DD ty1]

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
  (typeConstructor, _) <- splitAppliedConstructor tyS
  typeConstructor' <- Env.lookupTypeConstructor typeConstructor
  case typeConstructor' of
    Just (_, constructors) -> do
      guard (length branches == length constructors)
      let branchesCheck = zip constructors branches
      foldM_
        ( \_ (TypeDecl expCstr _ typCstr, branch) -> do
            (PatCon (Unbound.Embed cstr) xs, body) <- Unbound.unbind branch
            guard (expCstr == cstr)
            enterBranch xs typCstr $ checkType body ret
        )
        ()
        branchesCheck
    Nothing ->
      Env.err
        [ DD scrut,
          DS "is headed by",
          DD typeConstructor,
          DS "which is not a type constructor"
        ]
  where
    enterBranch :: [TName] -> Term -> TcMonad a -> TcMonad a
    enterBranch names typ k = do
      -- TODO: ensure that typ is already normalized in context
      typ' <- Equal.whnf typ
      case (names, typ') of
        (n : ns, TyPi eps a bnd) -> do
          let b = instantiate bnd (Var n)
          Env.extendCtx (Decl $ TypeDecl n eps a) $ enterBranch ns b k
        -- TODO: errors
        ([], TyPi _ _ _) ->
          Env.err
            [ DS "Unbound argument in pattern:",
              DD typ',
              DS "should be fully introduced."
            ]
        (n : _, _) ->
          Env.err
            [ DS "Too many arguments in pattern:",
              DD n,
              DS "is the first unused name."
            ]
        (_, _) -> k

-------------------------------------------------------------------------

-- | Make sure that the term is a "type" (i.e. that it has type 'Type')
tcType :: Term -> TcMonad ()
tcType tm = Env.withStage Irr $ checkType tm TyType

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
    TrustMe -> return ()
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

    -- We only check the type if the pattern matching has no return clause.
    -- Otherwise, we can just le it be handled by inferType.
    (Case scrut Nothing branches) -> checkMatch scrut ty' branches
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
tcEntry dat@(Data typ constructors) = do
  duplicateTypeBindingCheck typ
  Env.extendCtx dat $ tcConstructors constructors
  return $ AddCtx [dat]
  where
    tcConstructors :: [Constructor] -> TcMonad ()
    tcConstructors [] = return ()
    tcConstructors (h : t) = tcConstructor typ h >> tcConstructors t

tcConstructor :: TypeDecl -> Constructor -> TcMonad ()
tcConstructor dat@(TypeDecl dataTypeName _ _) (TypeDecl name _ cstrType) = do
  -- TODO: positivity check
  tcType cstrType
  iter cstrType
  where
    iter :: Term -> TcMonad ()
    iter typ = do
      typ' <- Equal.whnf typ
      case typ' of
        -- Go through the chain of arrows
        (TyPi _ a bnd) -> do
          (x, tyB) <- unbind bnd
          tcType a
          Env.extendCtxs [mkDecl x TyType] $ iter tyB
        -- And once the tail is reached
        _ -> do
          -- Extract the head
          (name, _) <- splitAppliedConstructor typ'
          -- which must by the type being defined.
          if name == dataTypeName
            then return ()
            else
              Env.err
                [ DS "The constructor",
                  DD typ',
                  DS "should be for type",
                  DD dataTypeName,
                  DS ", ",
                  DD name,
                  DS "found instead"
                ]

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
