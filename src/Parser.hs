{- pi-forall language -}

-- | A parsec-based parser for the concrete syntax
{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Redundant return" #-}
module Parser
  ( parseModuleFile,
    parseModuleImports,
    parseExpr,
    expr,
    decl,
    testParser,
  )
where

import Control.Monad.Except (MonadError (throwError))
import Control.Monad.State.Lazy hiding (join, fix)
import Data.List (foldl', intercalate)
import LayoutToken qualified as Token
import Syntax hiding (moduleImports)
import Text.Parsec hiding (Empty, State)
import Text.Parsec.Expr (Assoc (..), Operator (..), buildExpressionParser)
import Unbound.Generics.LocallyNameless qualified as Unbound
import Unbound.Generics.LocallyNameless (string2Name)

{-

Concrete syntax for the language:
Optional components in this BNF are marked with < >

  terms:
    a,b,A,B ::=
      Type                     Universe
    | x                        Variables   (must start with lowercase)
    | \ x . a                  Function definition
    | a b                      Application
    | (x : A) -> B             Pi type

    | (a : A)                  Annotations
    | (a)                      Parens
    | TRUSTME                  An axiom 'TRUSTME', inhabits all types
    | PRINTME                  Show the current goal and context

    | let x = a in b           Let expression

    | { x : A | B }            Dependent pair type
    | A * B                    Nondependent pair type (syntactic sugar)
    | (a, b)                   Pair introduction
    | let (x,y) = a in b       Pair elimination

    | a = b                    Equality type
    | Refl                     Equality proof
    | subst a by b             Type conversion
    | contra a                 Contra

    | \ [x <:A> ] . a          Irrelevant lambda
    | a [b]                    Irrelevant application
    | [x : A] -> B             Irrelevant function type

  declarations:

      foo : A                  Type declaration
      foo = a                  Definition

  Syntax sugar:

   - Nondependent function types, like:

         A -> B

      Get parsed as (_:A) -> B, with a wildcard name for the binder

   - Nondependent product types, like:

         A * B

      Get parsed as { _:A | B }, with a wildcard name for the binder

   - You can collapse lambdas, like:

         \ x [y] z . a

     This gets parsed as \ x . \ [y] . \ z . a

   - Natural numbers, like:

          3

      Get parsed as peano numbers (Succ (Succ (Succ Zero)))

-}

-- | Default name (for parsing 'A -> B' as '(_:A) -> B')
wildcardName :: TName
wildcardName = Unbound.string2Name "_"

liftError :: (MonadError e m) => Either e a -> m a
liftError (Left e) = throwError e
liftError (Right a) = return a

-- | Parse a module declaration from the given filepath.
parseModuleFile :: (MonadError ParseError m, MonadIO m) => String -> m Module
parseModuleFile name = do
  contents <- liftIO $ readFile name
  liftError $
    Unbound.runFreshM
      (runParserT (do whiteSpace; v <- moduleDef; eof; return v) [] name contents)

-- | Parse only the imports part of a module from the given filepath
parseModuleImports :: (MonadError ParseError m, MonadIO m) => String -> m Module
parseModuleImports name = do
  contents <- liftIO $ readFile name
  liftError $
    Unbound.runFreshM $
      runParserT (do whiteSpace; moduleImports) [] name contents

-- | Test an 'LParser' on a String.
testParser :: LParser t -> String -> Either ParseError t
testParser parser str =
  Unbound.runFreshM $
    runParserT (do whiteSpace; v <- parser; eof; return v) [] "<interactive>" str

-- | Parse an expression.
parseExpr :: String -> Either ParseError Term
parseExpr = testParser expr

-- * Lexer definitions

type LParser a =
  ParsecT
    String -- The input is a sequence of Char
    [Column]
    ( -- The internal state for Layout tabs

      Unbound.FreshM -- The internal state for generating fresh names,
    )
    a -- the type of the object being parsed

instance Unbound.Fresh (ParsecT s u Unbound.FreshM) where
  fresh = lift . Unbound.fresh

-- Based on Parsec's haskellStyle (which we can not use directly since
-- Parsec gives it a too specific type).
piforallStyle :: (Stream s m Char, Monad m) => Token.GenLanguageDef s u m
piforallStyle =
  Token.LanguageDef
    { Token.commentStart = "{-",
      Token.commentEnd = "-}",
      Token.commentLine = "--",
      Token.nestedComments = True,
      Token.identStart = letter,
      Token.identLetter = alphaNum <|> oneOf "_'",
      Token.opStart = oneOf ":!#$%&*+.,/<=>?@\\^|-",
      Token.opLetter = oneOf ":!#$%&*+.,/<=>?@\\^|-",
      Token.caseSensitive = True,
      Token.reservedNames =
        [ "Refl",
          "ind",
          "Type",
          "Prop",
          "===",
          "Set",
          "data",
          "where",
          "case",
          "of",
          "return",
          "with",
          "contra",
          "subst",
          "by",
          "let",
          "in",
          "as",
          "axiom",
          "TRUSTME",
          "PRINTME",
          "ord",
          "if",
          "then",
          "else",
          "()",
          "fix"
        ],
      Token.reservedOpNames =
        ["!", "?", "\\", ":", ".", ",", "<", "=", "+", "-", "*", "^", "()", "_", "|", "{", "}", ":=", "/"]
    }

tokenizer :: Token.GenTokenParser String [Column] (Unbound.FreshM)
layout :: forall a t. LParser a -> LParser t -> LParser [a]
(tokenizer, Token.LayFun layout) = Token.makeTokenParser piforallStyle "{" ";" "}"

identifier :: LParser String
identifier = Token.identifier tokenizer

whiteSpace :: LParser ()
whiteSpace = Token.whiteSpace tokenizer

variable :: LParser TName
variable =
  do
    i <- identifier
    return $ Unbound.string2Name i

wildcard :: LParser TName
wildcard = reservedOp "_" >> return wildcardName

varOrWildcard :: LParser TName
varOrWildcard = try wildcard <|> variable

colon, dot, comma :: LParser ()
colon = Token.colon tokenizer >> return ()
dot = Token.dot tokenizer >> return ()
comma = Token.comma tokenizer >> return ()

reserved, reservedOp :: String -> LParser ()
reserved = Token.reserved tokenizer
reservedOp = Token.reservedOp tokenizer

parens, brackets, braces :: LParser a -> LParser a
parens = Token.parens tokenizer
brackets = Token.brackets tokenizer
braces = Token.braces tokenizer

moduleImports :: LParser Module
moduleImports = do
  reserved "module"
  modName <- identifier
  reserved "where"
  imports <- layout importDef (return ())
  return $ Module modName imports []

moduleDef :: LParser Module
moduleDef = do
  reserved "module"
  modName <- identifier
  reserved "where"
  imports <- layout importDef (return ())
  decls <- layout decl (return ())

  return $ Module modName imports decls

importDef :: LParser ModuleImport
importDef = do reserved "import" >> (ModuleImport <$> importName)
  where
    importName = intercalate "/" <$> sepBy1 identifier (reservedOp "/")

--- Some tiny helpers

mkAbs :: TName -> Term -> Term
mkAbs x b = Lam (Unbound.bind x b)

applyAll :: Term -> [Term] -> Term
applyAll = foldl App

mkProd :: Term -> Term -> Term
mkProd l r = applyAll (Var $ string2Name "Prod") [l, r]

mkSigma :: TName -> Term -> Term -> Term
mkSigma x l r = applyAll (Var $ string2Name "Sigma") [l, mkAbs x r]

---
--- Top level declarations
---

decl, declDef, valDef, dataDef :: LParser Entry
decl = declDef <|> valDef <|> dataDef
declDef = do
  n <- try (variable >>= \v -> colon >> return v)
  ty <- expr
  return (mkDecl n ty)
valDef = do
  n <- try (do n <- variable; reservedOp "="; return n)
  val <- expr
  return $ Def n val
dataDef = do
  try (reserved "data")
  tName <- variable
  params <- telescope
  colon
  s <- expr
  reservedOp ":="
  constructors <- layout constructorDef (return ())
  return $ Data $ TypeConstructor tName (Unbound.bind params (s, constructors))
  where
    constructorDef = do
      name <- variable
      tele <- telescope
      colon
      typ <- expr
      return $ Constructor name [] (Unbound.bind tele typ)

telescope :: LParser Telescope
telescope = do
  bnds <- many binding
  let tele = foldr (\(x, xType) t -> Tele $ Unbound.rebind (x, Unbound.Embed xType) t) Empty bnds
  return tele

binding :: LParser (TName, Type)
binding =
  parens
    ( do
        name <- option wildcardName (try $ varOrWildcard >>= \n -> colon >> return n)
        typ <- expr
        return (name, typ)
    )

------------------------
------------------------
-- Terms
------------------------
------------------------

trustme :: LParser Term
trustme = reserved "TRUSTME" *> return (TrustMe)

printme :: LParser Term
printme = do
  pos <- getPosition
  reserved "PRINTME"
  return (Pos pos PrintMe)

refl :: LParser Term
refl =
  do
    reserved "Refl"
    return $ Refl

-- Expressions

expr, term, factor :: LParser Term
-- expr is the toplevel expression grammar
expr = do
  p <- getPosition
  Pos p <$> buildExpressionParser table term
  where
    table =
      [ [ifix AssocLeft "=" TyEq],
        [ifixM AssocRight "->" mkArrowType],
        [ifixM AssocRight "*" mkTupleType]
      ]
    ifix assoc op f = Infix (reservedOp op >> return f) assoc
    ifixM assoc op f = Infix (reservedOp op >> f) assoc
    mkArrowType =
      do
        n <- Unbound.fresh wildcardName
        return $ \tyA tyB ->
          TyPi tyA (Unbound.bind n tyB)
    mkTupleType =
      do
        n <- Unbound.fresh wildcardName
        return $ \tyA tyB ->
          mkSigma n tyA tyB

-- A "term" is either a function application or a constructor
-- application.  Breaking it out as a seperate category both
-- eliminates left-recursion in (<expr> := <expr> <expr>) and
-- allows us to keep constructors fully applied in the abstract syntax.
term = funapp <|> patternMatching

funapp :: LParser Term
funapp = do
  f <- factor
  foldl' App f <$> many factor

factor =
  choice
    [ Var <$> variable <?> "a variable",
      typen <?> "Type with mandatory level",
      prop <?> "Prop",
      set <?> "Set",
      lambda <?> "a lambda",
      fix <?> "a fixpoint",
      letExpr <?> "a let",
      substExpr <?> "a subst",
      refl <?> "Refl",
      contra <?> "a contra",
      trustme <?> "TRUSTME",
      printme <?> "PRINTME",
      sigmaTy <?> "a sigma type",
      expProdOrAnnotOrParens <?> "an explicit function type or annotated expression"
    ]

integer :: LParser Integer
integer = Token.integer tokenizer

typen :: LParser Term
typen = do
  reserved "Type"                      -- Parse the keyword 'Type' and consume trailing space
  TyType . LConst <$> integer          -- Parse the mandatory integer level and construct 'TyType'

prop :: LParser Term
prop =
  do
    reserved "Prop"
    return $ TyType LProp

set :: LParser Term
set = do
  reserved "Set"
  return $ TyType LSet

-- Lambda abstractions have the syntax '\x . e'
lambda :: LParser Term
lambda = do
  reservedOp "\\"
  binds <- many1 varOrWildcard
  dot
  body <- expr
  return $ foldr lam body binds
  where
    lam x m = Lam (Unbound.bind x m)

-- Fixpoints have the syntax 'fix f a1 ... ak [x] . e'
fix :: LParser Term
fix = do
  reservedOp "fix"
  fBind <- variable
  binds <- many variable
  xBind <- brackets variable
  dot
  body <- expr
  return $ Fix (Unbound.bind (fBind, binds) (Unbound.bind xBind body))

--
letExpr :: LParser Term
letExpr =
  do
    reserved "let"
    x <- variable
    reservedOp "="
    rhs <- expr
    reserved "in"
    Let rhs . Unbound.bind x <$> expr

-- Pattern matching
patternMatching :: LParser Term
patternMatching = do
  reserved "case"
  scrutinee <- term
  asClause <- option Nothing $ try (Just <$> (reserved "as" >> variable))
  inClause <- option Nothing $ try (Just . uncurry PatCon <$> (reserved "in" >> simplePattern))
  retClause <- option Nothing $ try (Just <$> (reserved "return" >> term))
  reserved "of"
  branches <- layout branch (return ())
  let predicate = DestructionPredicate $ Unbound.bind (asClause, inClause) retClause
  return $ Case scrutinee predicate branches
  where
    simplePattern = do
      constructor <- identifier
      bindings <- many varOrWildcard
      return (constructor, bindings)

    branch = do
      (constructor, bindings) <- simplePattern
      reservedOp "->"
      Branch . Unbound.bind (PatCon constructor bindings) <$> term

-- Function types have the syntax '(x:A) -> B'.  This production deals
-- with the ambiguity caused because these types, annotations and
-- regular old parens all start with parens.

data InParens = Colon Term Term | Comma Term Term | Nope Term

expProdOrAnnotOrParens :: LParser Term
expProdOrAnnotOrParens =
  let -- afterBinder picks up the return type of a pi
      afterBinder :: LParser Term
      afterBinder = do
        reservedOp "->"
        rest <- expr
        return rest

      -- before binder parses an expression in parens
      -- If it doesn't involve a colon, you get (Right tm)
      -- If it does, you get (Left tm1 tm2).  tm1 might be a variable,
      --    in which case you might be looking at an explicit pi type.
      beforeBinder :: LParser InParens
      beforeBinder =
        parens $
          choice
            [ do
                e1 <- try (term >>= (\e1 -> colon >> return e1))
                e2 <- expr
                return $ Colon e1 e2,
              -- do
              --   e1 <- try (term >>= (\e1 -> comma >> return e1))
              --   e2 <- expr
              --   return $ Comma e1 e2,
              Nope <$> expr
            ]
   in do
        bd <- beforeBinder
        case bd of
          Colon (Var x) a ->
            option
              (Ann (Var x) a)
              ( do
                  b <- afterBinder
                  return $ TyPi a (Unbound.bind x b)
              )
          Colon a b -> return $ Ann a b
          Comma a b ->
            return $ mkProd a b
          Nope a -> return a

-- subst e0 by e1
substExpr :: LParser Term
substExpr = do
  reserved "subst"
  a <- expr
  reserved "by"
  b <- expr
  return $ Subst a b

contra :: LParser Term
contra = do
  reserved "contra"
  witness <- expr
  return $ Contra witness

sigmaTy :: LParser Term
sigmaTy = do
  reservedOp "{"
  x <- variable
  colon
  a <- expr
  reservedOp "|"
  b <- expr
  reservedOp "}"
  return $ mkSigma x a b
