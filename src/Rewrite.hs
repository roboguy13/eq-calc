{-# LANGUAGE ScopedTypeVariables #-}

module Rewrite where

import           Language

import           Data.Maybe
import           Data.List

rewrites :: forall a. (Expr a -> Maybe (Expr a)) -> Expr a -> [Expr a]
rewrites f e0 = maybeCons (f e0) $ go e0
  where
    go :: Expr a -> [Expr a]
    go (Compose xs) = concat $ transpose $ map (atomRewrites f) xs

atomRewrites :: (Expr a -> Maybe (Expr a)) -> Atom a -> [Expr a]
atomRewrites f e0 = maybeCons (f' e0) (map toExpr (go e0))
  where
    f' = f . toExpr

    go (Var v) = []
    go (Constant name args) = map (Constant name) $ transpose $ map (rewrites f) args

toExpr :: Atom a -> Expr a
toExpr = Compose . (:[])

-- exprTranspose :: [Expr a] -> [[Atom a]]
-- exprTranspose = transpose . map getExpr

-- atomTranspose :: [[Atom a]] -> [Expr a]
-- atomTranspose = map Compose . transpose

maybeAppend :: Maybe [a] -> [a] -> [a]
maybeAppend Nothing = id
maybeAppend (Just xs) = (xs ++)

maybeCons :: Maybe a -> [a] -> [a]
maybeCons Nothing = id
maybeCons (Just x) = (x:)

