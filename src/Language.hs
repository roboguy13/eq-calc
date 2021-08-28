{-# LANGUAGE DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language where

import           Parser
import           Ppr

import           Control.Monad
import           Control.Applicative

import           Data.List

newtype ConstantName = ConstantName String deriving (Show, Eq)
newtype LawName      = LawName String deriving (Show, Eq)

data VarName = VarName String deriving (Show, Eq, Ord) --Char (Maybe Int)

varNameStr :: VarName -> String
varNameStr (VarName str) = str
-- varNameStr (VarName c i) = c:show i

instance Ppr VarName where ppr = varNameStr

newtype Expr a = Compose { getExpr :: [Atom a] }
  deriving (Functor, Foldable, Traversable, Semigroup, Show, Eq)

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
  deriving (Functor, Foldable, Traversable, Show, Eq)

toExpr :: Atom a -> Expr a
toExpr = Compose . (:[])

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
  deriving (Semigroup, Monoid, Show)


parseLawName :: Parser LawName
parseLawName = LawName <$> some (alphanum <|> char ' ')

lookupLaw :: [Law VarName] -> LawName -> Maybe (Law VarName)
lookupLaw laws name = find go laws
  where
    go (Law name' _)
      | name' == name = True
      | otherwise     = False

parseProofSteps :: [Law VarName] -> Parser (Maybe [ProofStep VarName])
parseProofSteps laws = do
  firstLhs <- parseExpr
  rest <- some go

  let eqs = makeEqs firstLhs rest

  pure $ mapM makeProofStep eqs
  where
    go = do
      some whitespace
      char '='
      some whitespace
      lawName <- bracketed (char '{') (char '}') parseLawName
      some whitespace
      e <- parseExpr
      pure (lawName, e)

    makeEqs x [] = error "parseProofSteps.makeEqs: []"
    makeEqs x [(lawName, y)] = [(lawName, x :=: y)]
    makeEqs x ((lawName, y):ys) = (lawName, x :=: y) : makeEqs y ys

    makeProofStep (lawName, eq) =
      let law_maybe = lookupLaw laws lawName
      in
      ProofStep <$> law_maybe <*> pure eq

parseLaw :: Parser (Law VarName)
parseLaw = do
  name <- bracketed (char '{') (char '}') parseLawName
  char ':'
  some whitespace
  lhs <- parseExpr
  some whitespace
  char '='
  some whitespace
  rhs <- parseExpr
  pure (Law name (lhs :=: rhs))

parseLaws :: Parser [Law VarName]
parseLaws = go -- <|> fmap (:[]) parseLaw
  where
    go = do --(parseLaw *> some whitespace *> parseLaws)
      law <- parseLaw
      fmap (law:) $ many (some (char '\n') *> parseLaw)
      -- fmap (law:) parseLaws

isReserved :: String -> Bool
isReserved = (`elem` [".", "=", "{", "}"])

parseConstantName :: Parser ConstantName
parseConstantName = do
  name <- some alphanum <|> operator
  guard (not (isReserved name))
  pure (ConstantName name)

parseExpr :: Parser (Expr VarName)
parseExpr = parens go2 <|> go2
  where
    go2 = go <|> fmap (Compose . (:[])) parseAtom
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

isVarName :: String -> Bool
isVarName [c] = c `elem` (['a'..'z'] ++ ['A'..'Z'])
isVarName [c,d] = isVarName [c] && d `elem` ['0'..'9']
isVarName _ = False

parseConstant :: Parser (ConstantName, [Expr VarName])
parseConstant = parens go <|> go
  where
    go = parseUnappliedOperator <|> parseInfix <|> do
      name@(ConstantName nameStr) <- parseConstantName
      guard (not (isVarName nameStr))
      args <- many (some whitespace *> parseArg)
      pure (name, args)

    parseArg = parens parseExpr <|> toExpr parseConstant <|> toExpr parseUnappliedOperator <|> toExpr parseInfix <|> fmap varName parseVarName

    toExpr :: Parser (ConstantName, [Expr a]) -> Parser (Expr a)
    toExpr = fmap (\(n, es) -> Compose [Constant n es])

    varName v = Compose [Var v]

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


