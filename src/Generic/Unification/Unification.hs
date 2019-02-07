--------------------------------------------------------------------------------
-- |
-- Module      :  Generic.Unification.Unification
-- Copyright   :  (C) 2018-19 Carlo Nucera
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Carlo Nucera <meditans@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module implements the unification algorithm described in `Efficient
-- functional Unification and Substitution` by A.Dijkstra. The essential feature
-- of the algorithm is that it is quite fast, and it dispenses with unification
-- checks during the unification phase (you can perform it when applying
-- substitutions directly). Further optimisations may come in future.
--
--------------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds, DefaultSignatures, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving        #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, TypeOperators #-}
{-# LANGUAGE UndecidableInstances                                 #-}

module Generic.Unification.Unification
  ( -- * The Unifiable typeclass
    Unifiable(unify, checkOccurs)
  , SubstitutableGenConstraints
  , UnificationError(..)

    -- * A concrete transformer
  , UnificationT(..)
  , evalUnificationT
  , runUnificationT
  ) where

import Generics.SOP hiding (fromList)
import Data.Typeable
import Data.Maybe (isJust, fromJust)
import Control.Monad.State
import Control.Monad.Except

import Control.Monad.Identity -- for testing, see below

import Generic.Unification.Term
import Generic.Unification.Term.Internal (errorRecOnSimpleTypes)
import Generic.Unification.Substitution
import qualified Generic.Unification.Substitution as Subst (singleton, lookup)

-- | Encodes what could go wrong in unification. The monad
-- `UnificationT` is instance of `MonadError` `UnificationError`.
data UnificationError =
  -- | Two terms that were unified have incompatible shapes.
    IncompatibleUnification
  -- | A term failed the occurs check (it was cyclic).
  | OccursCheckFailed
  deriving (Show)

-- | A monad transformer to capture the threading of a substitution and the
-- errors that can happen during unification. This is a monad transformer
-- because you may want to change the monads at the bottom of the stack, for
-- example to put there a non-determinism monad.
newtype UnificationT m a
  = Unification
  { unUnificationT :: StateT Substitution (ExceptT UnificationError m) a }
  deriving (Functor, Applicative, Monad, MonadState Substitution, MonadError UnificationError)

-- | Calculate the result of an UnificationT computation.
evalUnificationT :: (Monad m) => UnificationT m a -> m (Either UnificationError a)
evalUnificationT = runExceptT . ($ mempty) . evalStateT . unUnificationT

-- | Unwrap UnificationT to its meaning.
runUnificationT :: (Monad m) => UnificationT m a -> Substitution -> m (Either UnificationError (a, Substitution))
runUnificationT u s = runExceptT . ($ s) . runStateT . unUnificationT $ u

--------------------------------------------------------------------------------
-- Unifiable
--------------------------------------------------------------------------------

-- | A constraint synonym that indicates all the constraints a type should have
-- to be automatically part of the Unifiable class.
type SubstitutableGenConstraints a =
  ( Typeable a, Generic a, HasDatatypeInfo a
  , Eq a, Show a, Substitutable a
  , All2 (Compose Show Term)           (Code a)
  , All2 (Compose Eq Term)             (Code a)
  , All2 (And Unifiable Substitutable) (Code a))

-- | This is the class that offers the interface for unification. The user of
-- the library is not supposed to add instances to this class.
class (Substitutable a) => Unifiable a where
  {-# minimal unify, checkOccurs #-}
  -- | Unify two values in the monad. This operation does not perform the occur
  -- check, for performance reasons and because you may not need it (for example
  -- when using non-recursive structures). If you want to be sure that your
  -- terms do not contain cycles, use the following function.
  unify         :: (Monad m) => Term a -> Term a -> UnificationT m (Term a)
  unify ta tb = do { st <- get; uni st ta tb }
  -- | This function will perform the occurs check, returning an equivalent term
  -- or a `OccursCheckFailed` exception. If you want to explicitly observe the
  -- occurs check failure, use `@@` from the `Substitutable` class.
  checkOccurs :: (Monad m) => Term a -> UnificationT m (Term a)
  checkOccurs t = do
    s <- get
    case s @@ t of
      Nothing -> throwError OccursCheckFailed
      Just t2 -> pure t2

  uni :: (Monad m)
      => Substitution -> Term a -> Term a -> UnificationT m (Term a)
  default uni :: (SubstitutableGenConstraints a, Monad m)
      => Substitution -> Term a -> Term a -> UnificationT m (Term a)
  uni _ v@(Con a) (Con b)  | a == b     = pure v
                           | otherwise  = throwError IncompatibleUnification
  uni _ v@(Var i) (Var j)  | i == j     = pure v
  uni st (Var i) t         | isJust mbv = uni st (fromJust mbv) t
    where
      mbv = Subst.lookup @a i st
  uni st (Var i) t         | otherwise  = bindVar st i t
  uni st t       v@(Var _)              = uni st v t
  uni _ (Rec t1) (Rec t2)
    | sameConstructor t1 t2 =
      let
        mt1   = hliftA  (Comp . Just) t1
        emt1  = hexpand (Comp Nothing) mt1
        pairs = hliftA2 unsafePair emt1 t2
      in do
        Rec <$> hctraverse' (Proxy @(And Unifiable Substitutable))
                            (\(Comp (Pair s1 s2)) -> do
                               currSubst <- get
                               uni currSubst s1 s2)
                            pairs
    | otherwise = throwError IncompatibleUnification
  uni st (Con t1) t2@(Rec _) = uni st (expandTerm t1) t2
  uni st t1@(Rec _) (Con t2) = uni st t1 (expandTerm t2)

instance {-# overlappable #-} Unifiable Int where
  unify ta tb = do { st <- get; uni st ta tb }
  checkOccurs t = do
    s <- get
    case s @@ t of
      Nothing -> throwError OccursCheckFailed
      Just t2 -> pure t2
  uni _ v@(Con a) (Con b)  | a == b     = pure v
                           | otherwise  = throwError IncompatibleUnification
  uni _ v@(Var i) (Var j)  | i == j     = pure v
  uni st (Var i) t         | isJust mbv = uni st (fromJust mbv) t
    where
      mbv = Subst.lookup @Int i st
  uni st (Var i) t         | otherwise  = bindVar st i t
  uni st t       v@(Var _)              = uni st v t
  uni _ _ _                             = errorRecOnSimpleTypes

instance {-# overlappable #-} Unifiable Char where
  unify ta tb = do { st <- get; uni st ta tb }
  checkOccurs t = do
    s <- get
    case s @@ t of
      Nothing -> throwError OccursCheckFailed
      Just t2 -> pure t2
  uni _ v@(Con a) (Con b)  | a == b     = pure v
                           | otherwise  = throwError IncompatibleUnification
  uni _ v@(Var i) (Var j)  | i == j     = pure v
  uni st (Var i) t         | isJust mbv = uni st (fromJust mbv) t
    where
      mbv = Subst.lookup @Char i st
  uni st (Var i) t         | otherwise  = bindVar st i t
  uni st t       v@(Var _)              = uni st v t
  uni _ _ _                             = errorRecOnSimpleTypes

instance {-# overlappable #-} Unifiable String where
  unify ta tb = do { st <- get; uni st ta tb }
  checkOccurs t = do
    s <- get
    case s @@ t of
      Nothing -> throwError OccursCheckFailed
      Just t2 -> pure t2
  uni _ v@(Con a) (Con b)  | a == b     = pure v
                           | otherwise  = throwError IncompatibleUnification
  uni _ v@(Var i) (Var j)  | i == j     = pure v
  uni st (Var i) t         | isJust mbv = uni st (fromJust mbv) t
    where
      mbv = Subst.lookup @String i st
  uni st (Var i) t         | otherwise  = bindVar st i t
  uni st t       v@(Var _)              = uni st v t
  uni _ _ _                             = errorRecOnSimpleTypes

instance {-# overlappable #-} SubstitutableGenConstraints a => Unifiable a where
  unify ta tb = do { st <- get; uni st ta tb }
  checkOccurs t = do
    s <- get
    case s @@ t of
      Nothing -> throwError OccursCheckFailed
      Just t2 -> pure t2

-- | This function binds an int to a term in a substitution. Intended for
-- private module use.
bindVar
  :: forall m a. (Eq a, Eq (Term a), Show (Term a), Typeable a, Substitutable a, Monad m)
  => Substitution -> Int -> Term a -> UnificationT m (Term a)
bindVar st i t = do
  put (Subst.singleton i t <> st)
  pure t

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | A synonym for (,) that I use to zip together datatypes in the generic procedure.
data Pair a = Pair a a

-- Unfortunately I cannot express the fact that I will always have the Just
-- case, in the generic implementation of uni
unsafePair :: forall a. (:.:) Maybe Term a -> Term a -> (Pair :.: Term) a
unsafePair (Comp (Just t1)) t2 = Comp $ Pair t1 t2
unsafePair (Comp Nothing)   _  = error "Structures should be matched"

-- Convenience function
sameConstructor :: SOP a b -> SOP a b -> Bool
sameConstructor a b = hindex a == hindex b

--------------------------------------------------------------------------------
-- On not doing the occur check
--------------------------------------------------------------------------------

cons :: Term a -> Term [a] -> Term [a]
cons ta tas = Rec . SOP . S . Z $ ta :* tas :* Nil

a :: UnificationT Identity (Term [Int])
a = unify (Var 1) (cons (Con 1) (Var 1))

-- I want to trigger the occur check in this
b :: UnificationT Identity (Term [Int])
b = do
  t <- unify (Var 1) (cons (Con 1) (Var 1))
  checkOccurs t

-- >>> runIdentity $ runUnificationT a
-- Right (: (Con 1) (Var 1),Substitution { [Int] -> [(1,: (Con 1) (Var 1))] })
-- >>> runIdentity $ runUnificationT b
-- Left OccursCheckFailed
