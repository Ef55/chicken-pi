{- pi-forall language -}

-- | A parsec-based parser for the concrete syntax
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
import Control.Monad.State.Lazy hiding (join)
import Data.List (foldl')
import LayoutToken qualified as Token
import Syntax hiding (moduleImports)
import Text.Parsec hiding (Empty, State)
import Text.Parsec.Expr (Assoc (..), Operator (..), buildExpressionParser)
import Unbound.Generics.LocallyNameless qualified as Unbound

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
      (runParserT (do whiteSpace; moduleImports) [] name contents)

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
          "axiom",
          "TRUSTME",
          "PRINTME",
          "ord",
          "if",
          "then",
          "else",
          "()"
        ],
      Token.reservedOpNames =
        ["!", "?", "\\", ":", ".", ",", "<", "=", "+", "-", "*", "^", "()", "_", "|", "{", "}", ":="]
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
    importName = identifier

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
  return $ Data $ TypeConstructor tName s (Unbound.bind params constructors)
  where
    constructorDef = do
      name <- variable
      tele <- telescope
      colon
      typ <- expr
      return $ Constructor name (Unbound.bind tele typ)

telescope :: LParser Telescope
telescope = do
  bnds <- many binding
  let tele = foldr (\(x, xType) t -> Tele $ Unbound.rebind (x, Unbound.Embed xType) t) Empty bnds
  return tele

binding :: LParser (TName, Type)
binding = parens (do
  name <- option wildcardName (try $ varOrWildcard >>= \n -> colon >> return n)
  typ <- expr
  return (name, typ))

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
          TyPi Rel tyA (Unbound.bind n tyB)
    mkTupleType =
      do
        n <- Unbound.fresh wildcardName
        return $ \tyA tyB ->
          TySigma tyA (Unbound.bind n tyB)

-- A "term" is either a function application or a constructor
-- application.  Breaking it out as a seperate category both
-- eliminates left-recursion in (<expr> := <expr> <expr>) and
-- allows us to keep constructors fully applied in the abstract syntax.
term = funapp <|> patternMatching

funapp :: LParser Term
funapp = do
  f <- factor
  foldl' app f <$> many bfactor
  where
    bfactor =
      ((,Irr) <$> brackets expr)
        <|> ((,Rel) <$> factor)
    app e1 (e2, ep) = App e1 (Arg ep e2)

factor =
  choice
    [ Var <$> variable <?> "a variable",
      typen <?> "Type",
      lambda <?> "a lambda",
      try letPairExp <?> "a let pair",
      letExpr <?> "a let",
      substExpr <?> "a subst",
      refl <?> "Refl",
      contra <?> "a contra",
      trustme <?> "TRUSTME",
      printme <?> "PRINTME",
      impProd <?> "an implicit function type",
      sigmaTy <?> "a sigma type",
      expProdOrAnnotOrParens
        <?> "an explicit function type or annotated expression"
    ]

impOrExpVar :: LParser (TName, Epsilon)
impOrExpVar =
  try ((,Irr) <$> (brackets varOrWildcard))
    <|> (,Rel) <$> varOrWildcard

typen :: LParser Term
typen =
  do
    reserved "Type"
    return TyType

-- Lambda abstractions have the syntax '\x . e'
lambda :: LParser Term
lambda = do
  reservedOp "\\"
  binds <- many1 impOrExpVar
  dot
  body <- expr
  return $ foldr lam body binds
  where
    lam (x, ep) m = Lam ep (Unbound.bind x m)

--
letExpr :: LParser Term
letExpr =
  do
    reserved "let"
    x <- variable
    reservedOp "="
    rhs <- expr
    reserved "in"
    body <- expr
    return $ Let rhs (Unbound.bind x body)

letPairExp :: LParser Term
letPairExp = do
  reserved "let"
  reservedOp "("
  x <- variable
  reservedOp ","
  y <- variable
  reservedOp ")"
  reservedOp "="
  scrut <- expr
  reserved "in"
  a <- expr
  return $ LetPair scrut (Unbound.bind (x, y) a)

-- impProd - implicit dependent products
-- These have the syntax [x:a] -> b or [a] -> b .
impProd :: LParser Term
impProd =
  do
    (x, tyA) <-
      brackets
        ( try ((,) <$> variable <*> (colon >> expr))
            <|> ((,) <$> Unbound.fresh wildcardName <*> expr)
        )
    reservedOp "->"
    tyB <- expr
    return $ TyPi Irr tyA (Unbound.bind x tyB)

-- Pattern matching
patternMatching :: LParser Term
patternMatching = do
  reserved "case"
  scrutinee <- term
  ret <- Just <$> try (reserved "return" >> term) <|> pure Nothing
  reserved "of"
  branches <- layout branch (return ())
  return $ Case scrutinee ret branches
  where
    branch = do
      constructor <- identifier
      bindings <- many varOrWildcard
      reservedOp "->"
      body <- term
      return $ Branch $ Unbound.bind (PatCon constructor bindings) body

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
              do
                e1 <- try (term >>= (\e1 -> comma >> return e1))
                e2 <- expr
                return $ Comma e1 e2,
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
                  return $ TyPi Rel a (Unbound.bind x b)
              )
          Colon a b -> return $ Ann a b
          Comma a b ->
            return $ Prod a b
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
  return (TySigma a (Unbound.bind x b))
