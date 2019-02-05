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
-- functional Unification and Substitution` by A.Dijkstra. Further optimisations
-- may come in future.
--
--------------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts, FlexibleInstances                   #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications, TypeOperators, UndecidableInstances, ConstraintKinds, DefaultSignatures #-}

module Generic.Unification.Unification
  ( UnificationError(..)
  , UnificationT(..)
  , evalUnificationT
  , runUnificationT
  , unify
  , SubstitutableGenConstraints
  , Unifiable(unifyVal, checkOccurs)
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
import qualified Generic.Unification.Substitution as Subst (empty, singleton, lookup)

-- | An error to encode what could go wrong in the unification procedure: it may
-- fail, or it may fail a occur check.
data UnificationError = IncompatibleUnification | OccursCheckFailed
  deriving (Show)

-- | A monad for unification
newtype UnificationT m a
  = Unification
  { unUnificationT :: StateT Substitution (ExceptT UnificationError m) a }
  -- { unUnification :: ExceptT UnificationError (State Substitution) a }
  deriving (Functor, Applicative, Monad, MonadState Substitution, MonadError UnificationError)

-- | Get the result back
evalUnificationT :: (Monad m) => UnificationT m a -> m (Either UnificationError a)
evalUnificationT = runExceptT . ($ Subst.empty) . evalStateT . unUnificationT

-- | Get the result and the unferlying substitution back
runUnificationT :: (Monad m) => UnificationT m a -> m (Either UnificationError (a, Substitution))
runUnificationT = runExceptT . ($ Subst.empty) . runStateT . unUnificationT

-- | Convenience function to run the unification of two terms
unify :: (Monad m, Unifiable a) => Term a -> Term a -> m (Either UnificationError (Term a))
unify a b = evalUnificationT (unifyVal a b)

--------------------------------------------------------------------------------
-- Unifiable
--------------------------------------------------------------------------------

type SubstitutableGenConstraints a =
  ( Typeable a, Generic a, HasDatatypeInfo a
  , Eq a, Show a, Substitutable a
  , All2 (Compose Show Term)           (Code a)
  , All2 (Compose Eq Term)             (Code a)
  , All2 (And Unifiable Substitutable) (Code a))

-- | This is the class that offers the interface for unification. The user of
-- the library is not supposed to add instances to this class.
class (Substitutable a) => Unifiable a where
  {-# minimal unifyVal, checkOccurs #-}
  -- | Unify two values in the monad. This operation does not perform the occur
  -- check, for performance reasons and because you may not need it (for example
  -- when using non-recursive structures). If you want to be sure that your
  -- terms do not contain cycles, use the following function.
  unifyVal         :: (Monad m) => Term a -> Term a -> UnificationT m (Term a)
  -- | This function will perform the occurs check, returning an equivalent term
  -- or a `OccursCheckFailed` exception.
  checkOccurs :: (Monad m) => Term a -> UnificationT m (Term a)

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
  uni _ _ _ = throwError IncompatibleUnification

instance {-# overlappable #-} Unifiable Int where
  unifyVal ta tb = do { st <- get; uni st ta tb }
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
  unifyVal ta tb = do { st <- get; uni st ta tb }
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
  unifyVal ta tb = do { st <- get; uni st ta tb }
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
  unifyVal ta tb = do { st <- get; uni st ta tb }
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
  -- TODO Write the <> instance!!!
  put (Subst.singleton i t `union` st)
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
a = unifyVal (Var 1) (cons (Con 1) (Var 1))

-- I want to trigger the occur check in this
b :: UnificationT Identity (Term [Int])
b = do
  t <- unifyVal (Var 1) (cons (Con 1) (Var 1))
  checkOccurs t

-- >>> runIdentity $ runUnificationT a
-- Right (: (Con 1) (Var 1),Substitution { [Int] -> [(1,: (Con 1) (Var 1))] })
-- >>> runIdentity $ runUnificationT b
-- Left OccursCheckFailed
