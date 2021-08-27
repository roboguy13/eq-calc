{-# LANGUAGE DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language where

import           Parser
import           Ppr

import           Control.Monad
import           Control.Applicative

import           Data.List

newtype ConstantName = ConstantName String deriving (Show)
newtype LawName      = LawName String deriving (Show, Eq)

data VarName = VarName String deriving (Show) --Char (Maybe Int)

varNameStr :: VarName -> String
varNameStr (VarName str) = str
-- varNameStr (VarName c i) = c:show i

instance Ppr VarName where ppr = varNameStr

newtype Expr a = Compose { getExpr :: [Atom a] }
  deriving (Functor, Foldable, Traversable, Semigroup, Show)

instance Applicative Expr where
  pure x = Compose [pure x]
  (<*>) = ap

instance Monad Expr where
  Compose xs0 >>= f = Compose (go xs0)
    where
      go [] = []
      go (Var x : rest) =
        let Compose fx = f x
        in
        fx ++ go rest

data Atom a = Var a | Constant ConstantName [Expr a]
  deriving (Functor, Foldable, Traversable, Show)

instance Applicative Atom where
  pure = Var
  (<*>) = ap

instance Monad Atom where
  Var x >>= f = f x
  Constant c args >>= f = Constant c (map (Compose . map (>>= f) . getExpr) args)

data Equation a = Expr a :=: Expr a deriving Show
data Law a = Law LawName (Equation a) deriving Show

data ProofStep a = ProofStep (Law a) (Equation a) deriving Show

newtype Subst a = Subst [(a, Expr a)]
  deriving (Semigroup, Monoid)


parseLawName :: Parser LawName
parseLawName = LawName <$> some (alphanum <|> char ' ')

lookupLaw :: [Law VarName] -> LawName -> Maybe (Law VarName)
lookupLaw laws name = find go laws
  where
    go (Law name' _)
      | name' == name = True
      | otherwise     = False

parseProofStep :: [Law VarName] -> Parser (Maybe (ProofStep VarName))
parseProofStep laws = do
  lhs <- parseExpr
  some whitespace
  char '='
  some whitespace
  lawName <- bracketed (char '{') (char '}') parseLawName
  some whitespace
  rhs <- parseExpr

  let law_maybe = lookupLaw laws lawName

  pure (ProofStep <$> law_maybe <*> pure (lhs :=: rhs))

parseLaw :: Parser (Law VarName)
parseLaw = do
  name <- parseLawName
  char ':'
  many whitespace
  lhs <- parseExpr
  some whitespace
  char '='
  some whitespace
  rhs <- parseExpr
  pure (Law name (lhs :=: rhs))

parseLaws :: Parser [Law VarName]
parseLaws = some parseLaw

isReserved :: String -> Bool
isReserved = (`elem` [".", "=", "{", "}"])

parseConstantName :: Parser ConstantName
parseConstantName = do
  name <- some alphanum <|> operator
  guard (not (isReserved name))
  pure (ConstantName name)

parseExpr :: Parser (Expr VarName)
parseExpr = go <|> fmap (Compose . (:[])) parseAtom
  where
    go = do
      a <- parseAtom
      some whitespace
      char '.'
      some whitespace
      Compose e <- parseExpr
      pure (Compose (a:e))

parseAtom :: Parser (Atom VarName)
parseAtom = fmap (uncurry Constant) parseConstant <|> fmap Var parseVarName

parseVarName :: Parser VarName
parseVarName = fmap VarName (go <|> fmap (:[]) alpha)
  where
    go = do
      a <- alpha
      d <- digit
      pure [a,d]

parseConstant :: Parser (ConstantName, [Expr VarName])
parseConstant = parens go <|> go
  where
    go = parseUnappliedOperator <|> parseInfix <|> do
      name <- parseConstantName
      args <- many (whitespace *> parseArg)
      pure (name, args)

    parseArg = toExpr (parseConstant) <|> toExpr parseUnappliedOperator <|> parens parseExpr <|> toExpr parseInfix

    toExpr :: Parser (ConstantName, [Expr a]) -> Parser (Expr a)
    toExpr = fmap (\(n, es) -> Compose [Constant n es])

parseUnappliedOperator :: Parser (ConstantName, [Expr VarName])
parseUnappliedOperator = do
  name <- parens operator
  pure (ConstantName name, [])

parseInfix :: Parser (ConstantName, [Expr VarName])
parseInfix = parens $ do
  lhs <- parseExpr
  some whitespace
  opName <- operator
  guard (not (isReserved opName))
  some whitespace
  rhs <- parseExpr
  pure (ConstantName opName, [lhs, rhs])


