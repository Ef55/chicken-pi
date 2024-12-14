{- pi-forall language -}

-- | Utilities for managing a typechecking context.
module Environment
  ( TcMonad,
    runTcMonad,
    Env,
    emptyEnv,
    lookupTy,
    lookupTyMaybe,
    lookupDef,
    lookupHint,
    lookupConstructor,
    lookupTypeConstructor,
    lookupSmaller,
    getCtx,
    getLocalCtx,
    extendCtx,
    extendCtxs,
    extendCtxsGlobal,
    extendCtxMods,
    extendHints,
    extendSourceLocation,
    getSourceLocation,
    err,
    warn,
    extendErr,
    D (..),
    Err (..),
    freshWildcard,
  )
where

import Control.Monad.Except
  ( ExceptT,
    MonadError (..),
    MonadIO (..),
    runExceptT,
    unless,
  )
import Control.Monad.Identity
import Control.Monad.RWS (MonadWriter, tell)
import Control.Monad.Reader
  ( MonadReader (local),
    ReaderT (runReaderT),
    asks,
  )
import Control.Monad.Trans.Writer (WriterT (runWriterT))
import Data.Kind (Type)
import Data.Maybe (listToMaybe)
import GHC.Base (Alternative ((<|>)))
import PrettyPrint (D (..), Disp (..), Doc, SourcePos, render)
import Syntax
import Text.PrettyPrint.HughesPJ (nest, sep, text, vcat, ($$))
import Unbound.Generics.LocallyNameless qualified as Unbound
import qualified Data.Maybe as Maybe

-- | The type checking Monad includes a reader (for the
-- environment), freshness state (for supporting locally-nameless
-- representations), error (for error reporting), and IO
-- (for e.g.  warning messages).
type TcMonad = Unbound.FreshMT (ReaderT Env (ExceptT Err (WriterT [String] Identity)))

-- | Entry point for the type checking monad, given an
-- initial environment, returns either an error message
-- or some result.
runTcMonad :: Env -> TcMonad a -> (Either Err a, [String])
runTcMonad env m =
  let m1 = Unbound.runFreshMT m
      m2 = runReaderT m1 env
      m3 = runExceptT m2
      m4 = runWriterT m3
      m5 = runIdentity m4
   in m5

freshWildcard :: TcMonad TName
freshWildcard = Unbound.fresh (Unbound.string2Name "_")

-- | Marked locations in the source code
data SourceLocation where
  SourceLocation :: forall a. (Disp a) => SourcePos -> a -> SourceLocation

-- | Environment manipulation and accessing functions
-- The context 'gamma' is a list
data Env = Env
  { -- | elaborated term and datatype declarations
    ctx :: [Entry],
    -- | how long the tail of "global" variables in the context is
    --    (used to supress printing those in error messages)
    globals :: Int,
    -- | Type declarations: it's not safe to
    -- put these in the context until a corresponding term
    -- has been checked.
    hints :: [TypeDecl],
    -- | what part of the file we are in (for errors/warnings)
    sourceLocation :: [SourceLocation]
  }

-- | The initial environment.
emptyEnv :: Env
emptyEnv =
  Env
    { ctx = [],
      globals = 0,
      hints = [],
      sourceLocation = []
    }

instance Disp Env where
  disp :: Env -> Doc
  disp e = vcat [disp decl | decl <- ctx e]
  debugDisp :: Env -> Doc
  debugDisp e = vcat [debugDisp decl | decl <- ctx e]

-- | Find a name's user supplied type signature.
lookupHint :: (MonadReader Env m) => TName -> m (Maybe TypeDecl)
lookupHint v = do
  hints <- asks hints
  return $ listToMaybe [sig | sig <- hints, v == declName sig]

-- | Find a name's type in the context.
lookupTyMaybe ::
  forall m.
  (MonadReader Env m) =>
  TName ->
  m (Maybe TypeDecl)
lookupTyMaybe v = do
  ctx <- asks ctx
  go ctx
  where
    go :: [Entry] -> m (Maybe TypeDecl)
    go (Decl sig : ctx) = do
      let r1 = testDecl sig
      r2 <- go ctx
      return $ r1 <|> r2
    go (_ : ctx) = go ctx
    go [] = return Nothing

    testDecl :: TypeDecl -> Maybe TypeDecl
    testDecl decl =
      if v == declName decl then Just decl else Nothing

-- | Find the type of a name specified in the context
-- throwing an error if the name doesn't exist
lookupTy ::
  TName -> TcMonad TypeDecl
lookupTy v =
  do
    x <- lookupTyMaybe v
    gamma <- getLocalCtx
    case x of
      Just res -> return res
      Nothing ->
        err
          [ DS ("The variable " ++ show v ++ " was not found."),
            DS "in context",
            DD gamma
          ]

-- | Find a name's def in the context.
lookupDef ::
  (MonadReader Env m) =>
  TName ->
  m (Maybe Term)
lookupDef v = do
  ctx <- asks ctx
  return $ listToMaybe [a | Def v' a <- ctx, v == v']

-- | Find a datatype's declaration
lookupTypeConstructor ::
  (MonadReader Env m) =>
  TName ->
  m (Maybe TypeConstructor)
lookupTypeConstructor name = do
  ctx <- asks ctx
  return $ go ctx
  where
    go :: [Entry] -> Maybe TypeConstructor
    go ((Data tc) : ctx)
      | name == typeName tc = Just tc
      | otherwise = go ctx
    go (_ : ctx) = go ctx
    go [] = Nothing

lookupConstructor ::
  (MonadReader Env m) =>
  TName ->
  m (Maybe TypeConstructor)
lookupConstructor name = do
  ctx <- asks ctx
  return $ go ctx
  where
    go :: [Entry] -> Maybe TypeConstructor
    go ((Data tc) : ctx) = checkConstructors tc <|> go ctx
    go (_ : ctx) = go ctx
    go [] = Nothing

    checkConstructors :: TypeConstructor -> Maybe TypeConstructor
    checkConstructors tc@(TypeConstructor _ bnd) =
      let names = Unbound.runFreshM $ do
            (_, (_, cstrs)) <- Unbound.unbind bnd
            return $ map (\(Constructor n _ _) -> n) cstrs
       in if name `elem` names then Just tc else Nothing

lookupSmaller :: (MonadReader Env m) => Term -> TName -> m Bool
lookupSmaller t n = do
  ctx <- asks ctx
  return $ Maybe.isNothing $ go ctx
  where
    -- Nothing means that the relation was validated
    -- Note that since the environment is "backward" (i.e. the most recent
    -- additions appear first), we must perform the lookup starting from the
    -- end to ensure that the transitive closure is complete.
    go :: [Entry] -> Maybe [TName]
    go (Smaller t' n' : ctx) = do
      rels <- go ctx
      let exp =
            [n' | aeq t t']
              ++ concatMap (\n'' -> if aeq t' (Var n'') then [n'', n'] else [n'']) rels
      if n `elem` exp then Nothing else Just exp
    go (_ : ctx) = go ctx
    go [] = Just []

-- | Extend the context with a new entry
extendCtx :: (MonadReader Env m) => Entry -> m a -> m a
extendCtx d =
  local (\m@Env {ctx = cs} -> m {ctx = d : cs})

-- | Extend the context with a list of bindings
extendCtxs :: (MonadReader Env m) => [Entry] -> m a -> m a
extendCtxs ds =
  local (\m@Env {ctx = cs} -> m {ctx = ds ++ cs})

-- | Extend the context with a list of bindings, marking them as "global"
extendCtxsGlobal :: (MonadReader Env m) => [Entry] -> m a -> m a
extendCtxsGlobal ds =
  local
    ( \m@Env {ctx = cs} ->
        m
          { ctx = ds ++ cs,
            globals = length (ds ++ cs)
          }
    )

-- | Extend the context with a module
-- Note we must reverse the order.
extendCtxMod :: (MonadReader Env m) => Module -> m a -> m a
extendCtxMod m = extendCtxs (reverse $ moduleEntries m)

-- | Extend the context with a list of modules
extendCtxMods :: (MonadReader Env m) => [Module] -> m a -> m a
extendCtxMods mods k = foldr extendCtxMod k mods

-- | Get the complete current context
getCtx :: (MonadReader Env m) => m [Entry]
getCtx = asks ctx

-- | Get the prefix of the context that corresponds to local variables.
getLocalCtx :: (MonadReader Env m) => m [Entry]
getLocalCtx = do
  g <- asks ctx
  glen <- asks globals
  return $ take (length g - glen) g

-- | Push a new source position on the location stack.
extendSourceLocation :: (MonadReader Env m, Disp t) => SourcePos -> t -> m a -> m a
extendSourceLocation p t =
  local (\e@Env {sourceLocation = locs} -> e {sourceLocation = SourceLocation p t : locs})

-- | access current source location
getSourceLocation :: (MonadReader Env m) => m [SourceLocation]
getSourceLocation = asks sourceLocation

-- | Add a type hint
extendHints :: (MonadReader Env m) => TypeDecl -> m a -> m a
extendHints h = local (\m@Env {hints = hs} -> m {hints = h : hs})

-- | An error that should be reported to the user
data Err = Err [SourceLocation] Doc

-- | Augment the error message with addition information
extendErr :: (MonadError Err m) => m a -> Doc -> m a
extendErr ma msg' =
  ma `catchError` \(Err ps msg) ->
    throwError $ Err ps (msg $$ msg')

instance Semigroup Err where
  (<>) :: Err -> Err -> Err
  (Err src1 d1) <> (Err src2 d2) = Err (src1 ++ src2) (d1 `mappend` d2)

instance Monoid Err where
  mempty :: Err
  mempty = Err [] mempty

dispErr :: (forall a. (Disp a) => a -> Doc) -> Err -> Doc
dispErr disp (Err [] msg) = msg
dispErr disp (Err ((SourceLocation p term) : _) msg) =
  disp p
    $$ nest 2 msg
    $$ nest 2 (text "In the expression" $$ nest 2 (disp term))

instance Disp Err where
  disp :: Err -> Doc
  disp = dispErr disp
  debugDisp = dispErr debugDisp

-- | Throw an error
err :: (Disp a, MonadError Err m, MonadReader Env m) => [a] -> m b
err d = do
  loc <- getSourceLocation
  throwError $ Err loc (sep $ map disp d)

-- | Print a warning
warn :: (Disp a, MonadReader Env m, MonadWriter [String] m) => a -> m ()
warn e = do
  loc <- getSourceLocation
  tell ["warning: " ++ render (disp (Err loc (disp e)))]