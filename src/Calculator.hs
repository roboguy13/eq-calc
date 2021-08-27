-- An implementation of Richard Bird's equational calculator (from Thinking
-- Functionally With Haskell)

{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Calculator
  where

import           Data.List
import           Control.Applicative
import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Identity

class Ppr a where
  ppr :: a -> String

newtype ConstantName = SymbolName String
newtype LawName      = LawName String

data VarName = VarName Char (Maybe Int)

varNameStr :: VarName -> String
varNameStr (VarName c i) = c:show i

instance Ppr VarName where ppr = varNameStr

newtype Expr a = Compose [Atom a]
  deriving (Functor, Foldable, Traversable, Semigroup)

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

data Atom a = Var a | Constant ConstantName
  deriving (Functor, Foldable, Traversable)

instance Applicative Atom where
  pure = Var
  (<*>) = ap

instance Monad Atom where
  Var x >>= f = f x
  Constant c >>= _ = Constant c

data Equation a = Expr a :=: Expr a
data Law a = Law LawName (Equation a)

data ProofStep a = ProofStep (Law a) (Equation a)

newtype Subst a = Subst [(a, Expr a)]
  deriving (Semigroup, Monoid)

newtype CalcError = CalcError String

newtype Calculator a = Calculator (Either CalcError (Expr a))
  deriving (Functor, Foldable, Traversable)

instance Applicative Calculator where
  pure = calcExpr . pure
  (<*>) = ap

instance Monad Calculator where
  Calculator (Right (Compose xs0)) >>= f = Calculator $ go xs0
    where
      go [] = Right (Compose [])
      go (Var x : rest) =
        let Calculator fx = f x
            gr = go rest
        in
        liftA2 (<>) fx (go rest)

calcError :: String -> Calculator a
calcError = Calculator . Left . CalcError

calcExpr :: Expr a -> Calculator a
calcExpr = Calculator . Right

performSubst :: forall a. (Eq a, Ppr a) => Subst a -> Expr a -> Calculator a
performSubst st = (>>= go) . calcExpr
  where
    go :: a -> Calculator a
    go v =
      case substLookup st v of
        Nothing -> calcError $ "Cannot find variable " ++ ppr v ++ " in substitution."
        Just x -> calcExpr x

singleSubst :: a -> Expr a -> Subst a
singleSubst v e = Subst [(v, e)]

substLookup :: Eq a => Subst a -> a -> Maybe (Expr a)
substLookup (Subst st) v = lookup v st

unifyExprUsing :: forall a. Eq a => Subst a -> Expr a -> Expr a -> Maybe (Subst a)
unifyExprUsing subst0 (Compose lhs) (Compose rhs) = execStateT (go lhs rhs) subst0
  where
    go :: [Atom a] -> [Atom a] -> StateT (Subst a) Maybe ()
    go (_:_) [] = lift Nothing
    go [] (_:_) = lift Nothing
    go (Var x:xs) (Var y:ys) = do
      st <- get
      xE <- lift $ substLookup st x
      yE <- lift $ substLookup st y
      st' <- lift $ unifyExpr xE yE
      put st'
      go xs ys

unifyExpr :: Eq a => Expr a -> Expr a -> Maybe (Subst a)
unifyExpr = unifyExprUsing mempty

unifyUsing :: Eq a => Subst a -> Law a -> Equation a -> Either CalcError (Subst a)
unifyUsing subst0 (Law lawName (lawLhs :=: lawRhs)) (stepLhs :=: stepRhs) =
  case go of
    Nothing -> Left $ CalcError "Cannot unify" -- TODO: Descriptive error
    Just r -> Right r
  where
    go = do
      st <- unifyExprUsing subst0 stepLhs lawLhs
      unifyExprUsing st stepRhs lawRhs

verifyProofStep :: Eq a => Subst a -> ProofStep a -> Either CalcError (Subst a)
verifyProofStep subst0 (ProofStep eq law) = unifyUsing subst0 eq law

verifyProofSteps :: forall a. Eq a => [ProofStep a] -> Either CalcError (Subst a)
verifyProofSteps [] = pure mempty
verifyProofSteps xs = execStateT (mapM_ go xs) mempty
  where
    go :: ProofStep a -> StateT (Subst a) (Either CalcError) ()
    go step = do
      st <- get
      lift $ verifyProofStep st step
      pure ()

type Laws a = [(LawName, Law a)]

