-- From Thinking Functionally in Haskell by Richard Bird
{-# LANGUAGE ScopedTypeVariables #-}

module Rewrite (rewrites, match) where

import           Language
import           Subst
import           Ppr

import           Data.Maybe
import           Data.List

anyOne :: (a -> [a]) -> [a] -> [[a]]
anyOne f []     = []
anyOne f (x:xs) = [x':xs  | x' <- f x] ++
                  [x :xs' | xs' <- anyOne f xs]

rewrites :: (Ord a, Ppr a, Show a) => Equation a -> Expr a -> [Expr a]
rewrites eqn (Compose xs) = map Compose (rewritesSeg eqn xs ++ anyOne (rewritesA eqn) xs)

rewritesA eqn (Var v) = []
rewritesA eqn (Constant name es) = map (Constant name) (anyOne (rewrites eqn) es)


rewritesSeg :: (Ord a, Ppr a, Show a) => Equation a -> [Atom a] -> [[Atom a]]
rewritesSeg (e1 :=: e2) as =
  [as1 ++ getExpr (applySubst sub e2) ++ as3
    | (as1, as2, as3) <- segments as
    , sub <- match (e1, Compose as2)
  ]

segments as =
  [ (as1, as2, as3)
  | (as1, bs) <- splits as
  , (as2, as3) <- splits bs
  ]

splits :: [a] -> [([a], [a])]
splits []     = [([], [])]
splits (a:as) = ([], a:as) : [(a:as1, as2) | (as1, as2) <- splits as]

match :: Ord a => (Expr a, Expr a) -> [Subst a]
match = concatMap (combine . map matchA) . alignments

matchA :: Ord a => (Atom a, Expr a) -> [Subst a]
matchA (Var v, e) = [singleSubst v e]
matchA (Constant name1 es1, Compose [Constant name2 es2])
  | name1 == name2 = combine (map match (zip es1 es2))
matchA _ = []

cart :: [[a]] -> [[a]]
cart [] = [[]]
cart (xs:xss) = [x:ys | x <- xs, ys <- yss]
  where
    yss = cart xss

combine :: Ord a => [[Subst a]] -> [Subst a]
combine = concatMap unifyAllSubst . cart

parts :: Int -> [a] -> [[[a]]]
parts 0 [] = [[]]
parts 0 _  = []
parts n as =
  [bs:bss
  | (bs, cs) <- splits as
  , bss <- parts (n-1) cs
  ]

alignments :: (Expr a, Expr a) -> [[(Atom a, Expr a)]]
alignments (Compose as, Compose bs) =
  [zip as (map Compose bss) | bss <- parts n bs]
  where
    n = length as


unifySubst :: Ord a => Subst a -> Subst a -> [Subst a]
unifySubst sub1 sub2
  | compatible sub1 sub2 = [unionSubst sub1 sub2]
  | otherwise            = []

compatible (Subst []) _ = True
compatible _ (Subst []) = True
compatible (Subst sub1@((v1,e1):sub1')) (Subst sub2@((v2,e2):sub2'))
  | v1 <  v2 = compatible (Subst sub1') (Subst sub2)
  | v1 == v2 = if e1 == e2 then compatible (Subst sub1') (Subst sub2') else False
  | v1 >  v2 = compatible (Subst sub1) (Subst sub2')

unionSubst (Subst []) sub2 = sub2
unionSubst sub1 (Subst []) = sub1
unionSubst (Subst sub1@((v1,e1):sub1')) (Subst sub2@((v2,e2):sub2'))
  | v1 <  v2 = substPush (v1, e1) $ unionSubst (Subst sub1') (Subst sub2)
  | v1 == v2 = substPush (v1, e1) $ unionSubst (Subst sub1') (Subst sub2')
  | v1 >  v2 = substPush (v2, e2) $ unionSubst (Subst sub1)  (Subst sub2')

unifyAllSubst :: Ord a => [Subst a] -> [Subst a]
unifyAllSubst = foldr f [mempty]
  where
    f sub subs = concatMap (unifySubst sub) subs

