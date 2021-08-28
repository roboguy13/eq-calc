-- An implementation of Richard Bird's equational calculator (from Thinking
-- Functionally With Haskell)

{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module Calculator
  where

import           Language
import           Rewrite
import           Ppr

import           Data.List
import           Control.Applicative
import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Identity
import           Control.Monad.Except

import           Data.String

newtype CalcError = CalcError String
  deriving (Semigroup, Monoid)

instance IsString CalcError where
  fromString = CalcError

showCalcError :: CalcError -> String
showCalcError (CalcError str) = str

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

calcError :: String -> Calculator a
calcError = Calculator . Left . CalcError

calcExpr :: Expr a -> Calculator a
calcExpr = Calculator . Right

performSubst :: forall a. (Eq a, Show a, Ppr a) => Subst a -> Expr a -> Calculator a
performSubst st = (>>= go) . calcExpr
  where
    go :: a -> Calculator a
    go v = Calculator $ substLookup st v
      -- case substLookup st v of
      --   Nothing -> calcError $ "Cannot find variable " ++ ppr v ++ " in substitution."
      --   Just x -> calcExpr x

singleSubst :: a -> Expr a -> Subst a
singleSubst v e = Subst [(v, e)]

substLookup :: (Eq a, Show a) => Subst a -> a -> Either CalcError (Expr a)
substLookup (Subst st) v =
  case lookup v st of
    Nothing -> Left $ "Cannot find " <> fromString (show v) <> " in substitution " <> fromString (show st)
    Just x -> Right x

zipMap_ :: (Applicative (t (Either CalcError)), MonadTrans t) => (a -> b -> t (Either CalcError) ()) -> [a] -> [b] -> t (Either CalcError) ()
zipMap_ _ [] [] = pure ()
zipMap_ _ (_:_) [] = lift $ Left "Unification error: zipMap: wrong number of arguments"
zipMap_ _ [] (_:_) = lift $ Left "Unification error: zipMap: wrong number of arguments"
zipMap_ f (x:xs) (y:ys) = f x y *> zipMap_ f xs ys

extendSubst :: (Eq a, Show a, MonadState (Subst a) m, MonadError CalcError m) => a -> Expr a -> m ()
extendSubst var x = do
  subst@(Subst sts) <- get
  case substLookup subst var of
    Left _ -> put (Subst ((var, x):sts))
    Right y -> do
      subst' <- liftEither (unifyExprUsing subst x y) -- TODO: Is this correct?
      put subst'

unifyExprUsing :: forall a. (Eq a, Show a) => Subst a -> Expr a -> Expr a -> Either CalcError (Subst a)
unifyExprUsing subst0 lhs rhs = execStateT (go' lhs rhs) subst0
  where
    go :: [Atom a] -> [Atom a] -> StateT (Subst a) (Either CalcError) ()
    go [] [] = pure ()
    go (_:_) [] = lift $ Left "Unification error: Wrong number of arguments"
    go [] (_:_) = lift $ Left "Unification error: Wrong number of arguments"
    go (Var x:xs) (Var y:ys) 
      | x == y = go xs ys
      | otherwise = do
        st <- get
        xE <- lift $ substLookup st x
        yE <- lift $ substLookup st y
        st' <- lift $ unifyExpr xE yE
        put st'
        go xs ys
    go (Var v:xs) (y:ys) = do
      extendSubst v (Compose [y])
      go xs ys
    go (x:xs) (Var v:ys) = do
      extendSubst v (Compose [x])
      go xs ys
    go (Constant f argsF : xs) (Constant g argsG : ys) = do
      st <- get
      when (f /= g) $
        lift $ Left $ "Cannot unify " <> fromString (show f) <> " with " <> fromString (show g)

      zipMap_ go' argsF argsG

      go xs ys
    -- go x y = lift $ Left $ "Cannot unify " <> fromString (show x) <> " with " <> fromString (show y)

    go' (Compose xs) (Compose ys) = go xs ys

unifyExpr :: (Eq a, Show a) => Expr a -> Expr a -> Either CalcError (Subst a)
unifyExpr = unifyExprUsing mempty

unifyUsing :: (Eq a, Show a) => Subst a -> Law a -> Equation a -> Either CalcError (Subst a)
unifyUsing subst0 (Law lawName (lawLhs :=: lawRhs)) (stepLhs :=: stepRhs) = go
  -- case go of
  --   Nothing -> Left $ CalcError "Cannot unify" -- TODO: Descriptive error
  --   Just r -> Right r
  where
    go = do
      st <- unifyExprUsing subst0 stepLhs lawLhs
      unifyExprUsing st stepRhs lawRhs
      -- when (stepRhs /= lawRhs) $
      --   Left $ "original RHS and transformed RHS do not match:\n" <> fromString (show stepRhs) <> "\n\n" <> fromString (show lawRhs)

toMaybe :: Either a b -> Maybe b
toMaybe (Left x) = Nothing
toMaybe (Right y) = Just y

tryUnifyUsing :: (Eq a, Ppr a, Show a) => Subst a -> Expr a -> Law a -> Expr a -> Maybe (Expr a)
tryUnifyUsing subst0 stepRhs (Law lawName (lawLhs :=: lawRhs)) expr0 = do
  st <- toMaybe (unifyExprUsing subst0 expr0 lawLhs)
  st' <- toMaybe $ unifyExprUsing st lawRhs stepRhs

  toMaybe . runCalculator $ performSubst st' stepRhs

verifyProofStep :: (Eq a, Ppr a, Show a) => Subst a -> ProofStep a -> Either CalcError ()
verifyProofStep subst0 (ProofStep law@(Law (LawName lawName) _) eq@(stepLhs :=: stepRhs)) = --unifyUsing subst0 law eq *> pure ()
  case rewrites (tryUnifyUsing subst0 stepRhs law) stepLhs of
    [] -> Left ("Cannot unify using law " <> fromString lawName)
    (_:_) -> Right ()

verifyProofSteps :: forall a. (Eq a, Ppr a, Show a) => [ProofStep a] -> Either CalcError ()
verifyProofSteps [] = pure mempty
verifyProofSteps xs = evalStateT (mapM_ go xs) mempty
  where
    go :: ProofStep a -> StateT (Subst a) (Either CalcError) ()
    go step = do
      st <- get
      lift $ verifyProofStep st step
      pure ()

