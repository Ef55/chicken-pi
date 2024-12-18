{- pi-forall language -}

-- | A Pretty Printer.
module PrettyPrint (Disp (..), D (..), SourcePos, PP.Doc, PP.render, pp, debug) where

import Control.Monad (foldM)
import Control.Monad.Reader (MonadReader (ask, local), asks)
import Data.Maybe qualified as Maybe
import Data.Set qualified as S
import GHC.Base (Alternative ((<|>)))
import Syntax
import Text.ParserCombinators.Parsec.Error (ParseError)
import Text.ParserCombinators.Parsec.Pos (SourcePos, sourceColumn, sourceLine, sourceName)
import Text.PrettyPrint (Doc, ($$), (<+>))
import Text.PrettyPrint qualified as PP
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

-------------------------------------------------------------------------

-- * Classes and Types for Pretty Printing

-------------------------------------------------------------------------

-- | The 'Disp' class governs all types which can be turned into 'Doc's
-- The `disp` function is the main entry point for the pretty printer
class Disp d where
  disp :: d -> Doc
  debugDisp :: d -> Doc

  default disp :: (Display d) => d -> Doc
  disp d = display d initDI

  default debugDisp :: (Display d) => d -> Doc
  debugDisp d = display d initDI {showLongNames = True, showAnnots = True}

-- | Convenience entry point for the pretty printer
pp :: (Disp d) => d -> String
pp p = PP.render (disp p)

debug :: (Disp d) => d -> String
debug p = PP.render (debugDisp p)

-- | The 'Display' class is like the 'Disp' class. It qualifies
--   types that can be turned into 'Doc'.  The difference is that
--   this class uses the 'DispInfo' parameter and the Unbound library
--   to generate fresh names during printing.
class (Unbound.Alpha t) => Display t where
  -- | Convert a value to a 'Doc'.
  display :: t -> DispInfo -> Doc

-- | The data structure for information about the display
data DispInfo = DI
  { -- | should we show type annotations?
    showAnnots :: Bool,
    -- | names that have been used
    dispAvoid :: S.Set Unbound.AnyName,
    -- | current precedence level
    prec :: Int,
    -- | should we print internally-generated names, or user-friendly versions
    showLongNames :: Bool
  }

-- | Error message quoting
data D
  = -- | String literal
    DS String
  | -- | Displayable value
    forall a. (Disp a) => DD a
  | -- | Displayable list
    DL [D]

initDI :: DispInfo
initDI =
  DI
    { showAnnots = False,
      dispAvoid = S.empty,
      prec = 0,
      showLongNames = False
    }

-------------------------------------------------------------------------

-- * Disp Instances for quoting, errors, source positions, names

-------------------------------------------------------------------------

instance Disp D where
  disp (DS s) = PP.text s
  disp (DD d) = PP.nest 2 $ disp d
  disp (DL l) = PP.hsep $ map disp l

  debugDisp d@(DS s) = disp d
  debugDisp (DD d) = PP.nest 2 $ debugDisp d
  debugDisp (DL l) = PP.hsep $ map debugDisp l

instance Disp [D] where
  disp dl = PP.sep $ map disp dl
  debugDisp dl = PP.sep $ map disp dl

instance Disp ParseError where
  disp = PP.text . show
  debugDisp = disp

instance Disp SourcePos where
  disp p =
    PP.text (sourceName p)
      PP.<> PP.colon
      PP.<> PP.int (sourceLine p)
      PP.<> PP.colon
      PP.<> PP.int (sourceColumn p)
      PP.<> PP.colon
  debugDisp = disp

instance Disp (Unbound.Name Term) where
  disp = PP.text . Unbound.name2String
  debugDisp = PP.text . show

-------------------------------------------------------------------------

-- * Disp Instances for Term syntax (defaults to Display, see below)

-------------------------------------------------------------------------

instance Disp Level

instance Disp Term

instance Disp Module

instance Disp ModuleImport

instance Disp Entry

instance Disp [Entry]

instance Disp TypeDecl

instance Disp Constructor

instance Disp Telescope

instance Disp Pattern

------------------------------------------------------------------------

-- * Display Instances for Modules

-------------------------------------------------------------------------

instance Display Module where
  display m = do
    dn <- display (moduleName m)
    di <- mapM display (moduleImports m)
    de <- mapM display (moduleEntries m)
    pure $
      PP.text "module" <+> dn <+> PP.text "where"
        $$ PP.vcat di
        $$ PP.vcat de

instance Display ModuleImport where
  display (ModuleImport i) = pure $ PP.text "import" <+> disp i

instance Display [Entry] where
  display ds = do
    dd <- mapM display ds
    pure $ PP.vcat dd

instance Display Telescope where
  display Empty = const PP.empty
  display (Tele bnd) = do
    let ((x, Unbound.Embed xType), tele') = Unbound.unrebind bnd
    dx <- display x
    dt <- display xType
    dT <- display tele'
    return $
      PP.text "("
        PP.<> dx
        PP.<> PP.text ":"
        PP.<> dt
        PP.<> PP.text ")"
        PP.<> dT

instance Display TypeDecl where
  display decl = do
    dn <- display (declName decl)
    dt <- display (declType decl)
    pure $ dn <+> PP.text ":" <+> dt

instance Display Constructor where
  display decl =
    Unbound.lunbind (cstrType decl) $ \(t, r) -> do
      dn <- display (cstrName decl)
      dt <- display t
      dr <- display r
      pure $ dn <+> dt <+> PP.text ":" <+> dr

instance Display Entry where
  display (Def n term) = do
    dn <- display n
    dt <- display term
    pure $ dn <+> PP.text "=" <+> dt
  display (Decl decl) = display decl
  display (Data (TypeConstructor typeName pack)) =
    Unbound.lunbind pack $ \(params, (sort, cstrs)) -> do
      dtn <- display typeName
      dp <- display params
      ds <- display sort
      let top = PP.text "data" <+> dtn <+> dp <+> PP.text ":" <+> ds <+> PP.text ":="
      constructors <- mapM display cstrs
      return $ top $$ PP.nest 2 (PP.vcat constructors)
  display (Smaller l r) = do
    dl <- display l
    dr <- display r
    return $ dl <+> PP.text ">>" <+> dr

-------------------------------------------------------------------------

-- * Disp Instances for Prelude types

-------------------------------------------------------------------------

instance Disp String where
  disp = PP.text
  debugDisp = disp

instance Disp Int where
  disp = PP.text . show
  debugDisp = disp

instance Disp Integer where
  disp = PP.text . show
  debugDisp = disp

instance Disp Double where
  disp = PP.text . show
  debugDisp = disp

instance Disp Float where
  disp = PP.text . show
  debugDisp = disp

instance Disp Char where
  disp = PP.text . show
  debugDisp = disp

instance Disp Bool where
  disp = PP.text . show
  debugDisp = disp

dispMaybe :: (t -> Doc) -> Maybe t -> Doc
dispMaybe disp m = case m of
  (Just a) -> PP.text "Just" <+> disp a
  Nothing -> PP.text "Nothing"

instance (Disp a) => Disp (Maybe a) where
  disp = dispMaybe disp
  debugDisp = dispMaybe debugDisp

dispEither :: (Disp a, Disp b) => (forall a. (Disp a) => a -> Doc) -> Either a b -> Doc
dispEither disp e = case e of
  (Left a) -> PP.text "Left" <+> disp a
  (Right a) -> PP.text "Right" <+> disp a

instance (Disp a, Disp b) => Disp (Either a b) where
  disp = dispEither disp
  debugDisp = dispEither debugDisp

-------------------------------------------------------------------------

-- * Display instances for Prelude types used in AST

-------------------------------------------------------------------------

instance Display String where
  display = return . PP.text

instance Display Int where
  display = return . PP.text . show

instance Display Integer where
  display = return . PP.text . show

instance Display Double where
  display = return . PP.text . show

instance Display Float where
  display = return . PP.text . show

instance Display Char where
  display = return . PP.text . show

instance Display Bool where
  display = return . PP.text . show

-------------------------------------------------------------------------

-- * Display instances for Terms

-------------------------------------------------------------------------

levelApp :: Int
levelApp = 10

levelIf :: Int
levelIf = 0

levelLet :: Int
levelLet = 0

levelCase :: Int
levelCase = 0

levelLam :: Int
levelLam = 0

levelPi :: Int
levelPi = 0

levelSigma :: Int
levelSigma = 0

levelProd :: Int
levelProd = 0

levelArrow :: Int
levelArrow = 5

withPrec :: (MonadReader DispInfo m) => Int -> m a -> m a
withPrec p t =
  local (\d -> d {prec = p}) t

parens :: Bool -> Doc -> Doc
parens b = if b then PP.parens else id

brackets :: Bool -> Doc -> Doc
brackets b = if b then PP.brackets else id

instance Display (Unbound.Name Term) where
  display n = do
    b <- ask showLongNames
    return (if b then debugDisp n else disp n)

instance Display Level where
  display LProp = return $ PP.text "Prop"
  display LSet = return $ PP.text "Set"
  display (LConst l) = do
    i <- display l
    return $ PP.text "Type" <+> i


instance Display Term where
  display (TyType l) = display l
  display (Var n) = display n
  display a@(Lam b) = do
    n <- ask prec
    (binds, body) <- withPrec levelLam $ gatherBinders a
    return $ parens (levelLam < n) $ PP.hang (PP.text "\\" PP.<> PP.sep binds PP.<> PP.text ".") 2 body
  display (App f x) = do
    n <- ask prec
    df <- withPrec levelApp (display f)
    dx <- withPrec (levelApp + 1) (display x)
    return $ parens (levelApp < n) $ df <+> dx
  display (TyPi a bnd) = do
    Unbound.lunbind bnd $ \(n, b) -> do
      p <- ask prec
      lhs <-
        if n `elem` toListOf Unbound.fv b
          then do
            dn <- display n
            da <- withPrec 0 (display a)
            return $ PP.parens (dn <+> PP.colon <+> da)
          else withPrec (levelArrow + 1) (display a)
      db <- withPrec levelPi (display b)
      return $ parens (levelArrow < p) $ lhs <+> PP.text "->" <+> db
  display (Ann a b) = do
    sa <- ask showAnnots
    if sa
      then do
        da <- withPrec 0 (display a)
        db <- withPrec 0 (display b)
        return $ PP.parens (da <+> PP.text ":" <+> db)
      else display a
  display (Pos _ e) = display e
  display TrustMe = do
    return $ PP.text "TRUSTME"
  display PrintMe = do
    return $ PP.text "PRINTME"
  display (Let a bnd) = do
    Unbound.lunbind bnd $ \(x, b) -> do
      p <- ask prec
      da <- display a
      dx <- display x
      db <- display b
      return $
        parens (levelLet < p) $
          PP.sep
            [ PP.text "let"
                <+> dx
                <+> PP.text "="
                <+> da
                <+> PP.text "in",
              db
            ]
  display (Subst a b) = do
    p <- asks prec
    da <- withPrec 0 $ display a
    db <- withPrec 0 $ display b
    return $
      parens (levelPi < p) $
        PP.fsep
          [ PP.text "subst" <+> da,
            PP.text "by" <+> db
          ]
  display (TyEq a b) = do
    p <- ask prec
    da <- withPrec (levelApp + 1) $ display a
    db <- withPrec (levelApp + 1) $ display b
    return $ PP.parens $ (da <+> PP.text "=" <+> db)
  display Refl = do
    return $ PP.text "Refl"
  display (Contra ty) = do
    p <- ask prec
    dty <- display ty
    return $ parens (levelPi < p) $ PP.text "contra" <+> dty
  display (Case scrut dPredicate cases) = do
    p <- asks prec
    ds <- withPrec 0 $ display scrut
    dp <- display dPredicate
    db <- withPrec 0 $ mapM (display . getBranch) cases
    let top = PP.text "case" <+> ds <+> dp <+> PP.text "of"
    return $
      parens (levelCase < p) $
        if null cases then top <+> PP.text "{ }" else top $$ PP.nest 2 (PP.vcat db)
  display (Fix bnd) =
    Unbound.lunbind bnd $ \((f, xs), bnd2) -> Unbound.lunbind bnd2 $ \(x, body) -> do
      n <- ask prec
      df <- display f
      dxs <- mapM display xs
      dx <- display x
      db <- display body
      return $ parens (levelLam < n) $ PP.hang (PP.text "fix" <+> df <+> PP.sep dxs <+> PP.text "[" <+> dx <+> PP.text "]" <+> PP.text ".") 2 db
  display (Guarded by t) = do
    db <- display by
    dt <- withPrec 0 $ display t
    return $ PP.text "[" <+> db <+> PP.text "|" <+> dt <+> PP.text "]"

instance Display DestructionPredicate where
  display (DestructionPredicate bnd) = Unbound.lunbind bnd $ \((mAs, mIn), mRet) -> do
    dAs <- maybeDisplay mAs $ \r -> const (PP.text "as ") <> display r
    dPat <- maybeDisplay mIn $ \r -> const (PP.text "in ") <> display r
    dRet <- maybeDisplay mRet $ \r -> const (PP.text "return ") <> display r
    return $ dAs <+> dPat <+> dRet

instance Display Pattern where
  display (PatCon cstrName bindings) = do
    cstr <- display cstrName
    args <- mapM display bindings
    return $ cstr <+> PP.fsep args

instance Display (Unbound.Bind Pattern Term) where
  display caze = Unbound.lunbind caze $ \(pat, branch) ->
    do
      dp <- display pat
      body <- display branch
      return $
        PP.hang
          ( PP.fsep
              [ dp,
                PP.text "->"
              ]
          )
          2
          body

-------------------------------------------------------------------------

-- * Helper functions for displaying terms

-------------------------------------------------------------------------

gatherBinders :: Term -> DispInfo -> ([Doc], Doc)
gatherBinders (Lam b) =
  Unbound.lunbind b $ \(n, body) -> do
    dn <- display n
    let db = dn
    (rest, body') <- gatherBinders body
    return (db : rest, body')
gatherBinders body = do
  db <- display body
  return ([], db)

maybeDisplay :: Maybe a -> (a -> DispInfo -> Doc) -> DispInfo -> Doc
maybeDisplay Nothing _ = return PP.empty
maybeDisplay (Just a) p = p a

-------------------------------------------------------------------------

-- * LFresh instance for DisplayInfo reader monad

-------------------------------------------------------------------------

instance Unbound.LFresh ((->) DispInfo) where
  lfresh nm = do
    let s = Unbound.name2String nm
    di <- ask
    return $
      head
        ( filter
            (\x -> Unbound.AnyName x `S.notMember` dispAvoid di)
            (map (Unbound.makeName s) [0 ..])
        )
  getAvoids = asks dispAvoid
  avoid names = local upd
    where
      upd di =
        di
          { dispAvoid =
              S.fromList names `S.union` dispAvoid di
          }