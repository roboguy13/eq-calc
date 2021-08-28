{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Subst where

import           Language
import           Ppr

import           Data.String

import           Control.Monad.State
import           Control.Monad.Except

import           Control.Applicative

newtype CalcError = CalcError String
  deriving (Semigroup, Monoid)

instance IsString CalcError where
  fromString = CalcError

newtype Calculator a = Calculator { runCalculator :: Either CalcError (Expr a) }
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

      go (Constant name args : rest) =
        let f_args = sequenceA $ map (runCalculator . (>>= f) . Calculator . Right) args
        in
        liftA2 ((<>) . toExpr)
               (fmap (Constant name) f_args)
               (go rest)

substPush :: (a, Expr a) -> Subst a -> Subst a
substPush x (Subst xs) = Subst (x:xs)

calcError :: String -> Calculator a
calcError = Calculator . Left . CalcError

calcExpr :: Expr a -> Calculator a
calcExpr = Calculator . Right

performSubst :: forall a. (Eq a, Show a, Ppr a) => Subst a -> Expr a -> Calculator a
performSubst st = (>>= go) . calcExpr
  where
    go :: a -> Calculator a
    go v = Calculator $ substLookup st v

applySubst :: forall a. (Eq a, Show a, Ppr a) => Subst a -> Expr a -> Expr a
applySubst st e0 =
  case performSubst st e0 of
    Calculator (Left _) -> e0
    Calculator (Right e) -> e

singleSubst :: a -> Expr a -> Subst a
singleSubst v e = Subst [(v, e)]

substLookup :: (Eq a, Show a) => Subst a -> a -> Either CalcError (Expr a)
substLookup (Subst st) v =
  case lookup v st of
    Nothing -> Left $ "Cannot find " <> fromString (show v) <> " in substitution " <> fromString (show st)
    Just x -> Right x

