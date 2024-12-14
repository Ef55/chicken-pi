{- pi-forall language -}

-- | Compare two terms for equality
module Equal
  ( whnf,
    equate,
    unify,
    equateLevels,
    unconstruct,
    maybeUnconstruct,
    instantiateConstructorType,
  )
where

import Control.Monad (foldM, guard, when)
import Control.Monad.Error.Class (catchError)
import Control.Monad.Except
  ( MonadError,
    unless,
    zipWithM,
    zipWithM_,
  )
import Control.Monad.RWS (MonadReader)
import Data.Maybe qualified as Maybe
import Environment (D (DD, DL, DS), Env, Err, TcMonad)
import Environment qualified as Env
import GHC.Base (Alternative ((<|>)))
import Syntax
import Unbound.Generics.LocallyNameless qualified as Unbound

-- | Compare two levels for equality
equateLevels :: Level -> Level -> TcMonad ()
equateLevels l1 l2 = do
  if l1 == l2
    then return ()
    else do
      gamma <- Env.getLocalCtx
      Env.err
        [ DS "Universe level mismatch: expected level",
          DD l2,
          DS "but found level",
          DD l1,
          DS "in context:",
          DD gamma
        ]

-- | compare two expressions for equality
-- first check if they are alpha equivalent then
-- if not, weak-head normalize and compare
-- throw an error if they cannot be matched up
equate :: Term -> Term -> TcMonad ()
equate t1 t2 | Unbound.aeq t1 t2 = return ()
equate t1 t2 = do
  n1 <- whnf t1
  n2 <- whnf t2
  case (n1, n2) of
    (TyType l1, TyType l2) -> do
      equateLevels l1 l2
    (Var x, Var y) | x == y -> return ()
    (Lam bnd1, Lam bnd2) -> do
      (_, b1, b2) <- unbind2 bnd1 bnd2
      equate b1 b2
    (Fix bnd1, Fix bnd2) -> do
      ubnd <- Unbound.unbind2 bnd1 bnd2
      case ubnd of
        Nothing -> tyErr n1 n2
        Just (_, bnd1', _, bnd2') -> do
          ubnd' <- Unbound.unbind2 bnd1' bnd2'
          case ubnd' of
            Nothing -> tyErr n1 n2
            Just (_, body1, _, body2) -> equate body1 body2
    (App a1 a2, App b1 b2) ->
      equate a1 b1 >> equate a2 b2
    (TyPi tyA1 bnd1, TyPi tyA2 bnd2) -> do
      (_, tyB1, tyB2) <- unbind2 bnd1 bnd2
      equate tyA1 tyA2
      equate tyB1 tyB2
    (TrustMe, TrustMe) -> return ()
    (PrintMe, PrintMe) -> return ()
    (Let rhs1 bnd1, Let rhs2 bnd2) -> do
      (x, body1, body2) <- unbind2 bnd1 bnd2
      equate rhs1 rhs2
      equate body1 body2
    (TyEq a b, TyEq c d) -> do
      equate a c
      equate b d
    (Refl, Refl) -> return ()
    (Subst at1 pf1, Subst at2 pf2) -> do
      equate at1 at2
      equate pf1 pf2
    (Contra a1, Contra a2) ->
      equate a1 a2
    -- For case _ of, we ignore the destruction predicate
    (Case s1 _ b1s, Case s2 _ b2s) -> do
      equate s1 s2
      when (length b1s /= length b2s) (tyErr n1 n2)
      mapM_
        ( \(bn1, bn2) -> do
            m <- Unbound.unbind2 (getBranch bn1) (getBranch bn2)
            case m of
              Nothing -> do
                tyErr n1 n2
              Just (_, b1, _, b2) -> equate b1 b2
        )
        (zip b1s b2s)
    (_, _) -> tyErr n1 n2
  where
    tyErr n1 n2 = do
      gamma <- Env.getLocalCtx
      Env.err
        [ DS "Expected",
          DD n2,
          DS "but found",
          DD n1,
          DS "in context:",
          DD gamma
        ]

-------------------------------------------------------

-------------------------------------------------------

-- | Convert a term to its weak-head normal form.
whnf :: Term -> TcMonad Term
whnf (Var x) = do
  maybeDef <- Env.lookupDef x
  case maybeDef of
    (Just d) -> whnf d
    _ -> return (Var x)
whnf (App t1 t2) = do
  t1' <- whnf t1
  case linearize t1' [] of
    [Lam bnd] -> whnf $ instantiate bnd t2
    f@(Fix bnd) : args -> do
      ((self, xs), bnd') <- Unbound.unbind bnd
      -- Fix can only be reduced if it is applied up to the recursive parameter.
      if length xs == length args
        then whnf $ Unbound.substs ((self, f) : zip xs args) (Unbound.instantiate bnd' [t2])
        else return $ App t1' t2
    _ -> return $ App t1' t2
  where
    linearize :: Term -> [Term] -> [Term]
    linearize (App l r) a = linearize l (r : a)
    linearize t a = t : a
whnf c@(Case s pred branches) = do
  ns <- whnf s
  sb <- pickBranch ns branches
  case sb of
    Just (b, s) -> whnf $ Unbound.substs s b
    Nothing -> return $ Case ns pred branches

-- ignore/remove type annotations and source positions when normalizing
whnf (Ann tm _) = whnf tm
whnf (Pos _ tm) = whnf tm
whnf (Let rhs bnd) = do
  whnf (instantiate bnd rhs)
whnf (Subst tm pf) = do
  pf' <- whnf pf
  case pf' of
    Refl -> whnf tm
    _ -> return (Subst tm pf')

-- all other terms are already in WHNF
-- don't do anything special for them
whnf tm = return tm

-- | Looks for a matching branch in a list of branch, in order.
-- If a match is found, return the body of the matched branch, as well as
-- the (set of) bindings defined in the pattern.
pickBranch ::
  Term ->
  [Branch] ->
  TcMonad (Maybe (Term, [(TName, Term)]))
pickBranch s branches = do
  c <- unconstruct s
  r <- mapM (tryBranch c) branches
  return $ foldl (<|>) Nothing r
  where
    tryBranch :: (TName, [Term]) -> Branch -> TcMonad (Maybe (Term, [(TName, Term)]))
    tryBranch (constructor, args) bnd = do
      (PatCon cstrStr patVars, b) <- Unbound.unbind (getBranch bnd)
      let cstr :: TName = Unbound.string2Name cstrStr
      if constructor == cstr
        then do
          typeArgs <- instantiateConstructorType cstr args
          let substPat = zip patVars (drop (length args - length patVars) args)
          return $ Just (b, substPat)
        else return Nothing

-- | 'Unify' the two terms, producing a list of definitions that
-- must hold for the terms to be equal
-- If the terms are already equal, succeed with an empty list
-- If there is an obvious mismatch, fail with an error
-- If either term is "ambiguous" (i.e. neutral), give up and
-- succeed with an empty list
unify :: [TName] -> Term -> Term -> TcMonad [Entry]
unify ns tx ty = do
  txnf <- whnf tx
  tynf <- whnf ty
  if Unbound.aeq txnf tynf
    then return []
    else case (txnf, tynf) of
      (Var x, Var y) | x == y -> return []
      (Var y, yty) | y `notElem` ns -> return [Def y yty]
      (yty, Var y) | y `notElem` ns -> return [Def y yty]
      (TyEq a1 a2, TyEq b1 b2) -> (++) <$> unify ns a1 b1 <*> unify ns a2 b2
      (Lam bnd1, Lam bnd2) -> do
        (x, b1, b2) <- unbind2 bnd1 bnd2
        unify (x : ns) b1 b2
      (TyPi tyA1 bnd1, TyPi tyA2 bnd2) -> do
        (x, tyB1, tyB2) <- unbind2 bnd1 bnd2
        ds1 <- unify ns tyA1 tyA2
        ds2 <- unify (x : ns) tyB1 tyB2
        return (ds1 ++ ds2)
      _ ->
        if amb txnf || amb tynf
          then return []
          else Env.err [DS "Cannot equate", DD txnf, DS "and", DD tynf]

-- | Is a term "ambiguous" when it comes to unification?
-- In general, elimination forms are ambiguous because there are multiple
-- solutions.
amb :: Term -> Bool
amb (App t1 t2) = True
amb (Subst _ _) = True
-- (Case _ _ _) = True ???
amb _ = False

-------------------------------------------------------

-- | "Unconstruct" an applied constructor (or function, but
-- why would you do that?), and return its name and arguments.
maybeUnconstruct ::
  Term ->
  Maybe (TName, [Term])
maybeUnconstruct term0 = iter (strip term0) []
  where
    iter :: Term -> [Term] -> Maybe (TName, [Term])
    iter term acc = case term of
      App l r -> iter l (r : acc)
      (Var name) -> return (name, acc)
      _ -> Nothing

unconstruct ::
  Term ->
  TcMonad (TName, [Term])
unconstruct term = case maybeUnconstruct term of
  Just v -> return v
  _ ->
    Env.err
      [ DS "Expected constructor at head",
        DD term,
        DS "is not a sequence of applications headed by a variable."
      ]

maybeInstantiateConstructorType :: TName -> [Term] -> TcMonad (Maybe [Term])
maybeInstantiateConstructorType cstrName args = do
  (TypeDecl _ typ) <- Env.lookupTy cstrName
  let app =
        foldM
          ( \f a -> case f of
              TyPi _ bnd -> return $ Unbound.instantiate bnd [a]
              _ -> Nothing
          )
          typ
          args
  case app of
    Nothing -> return Nothing
    Just app -> do
      red <- whnf app
      return $ snd <$> maybeUnconstruct red

instantiateConstructorType :: TName -> [Term] -> TcMonad [Term]
instantiateConstructorType name args =
  maybeInstantiateConstructorType name args >>= \r ->
    case r of
      Just v -> return v
      _ ->
        Env.err
          [ DS "Instantiation of constructor",
            DD name,
            DS "with arguments",
            DL $ DD <$> args,
            DS "failed."
          ]