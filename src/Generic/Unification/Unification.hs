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
{-# LANGUAGE TypeApplications, TypeOperators, UndecidableInstances #-}

module Generic.Unification.Unification
  ( UnificationError(..)
  , UnificationT(..)
  , evalUnificationT
  , runUnificationT
  , unify
  , Unifiable(unifyVal)
  ) where

import Generics.SOP hiding (fromList)
import Data.Typeable
import Data.Maybe (isJust, fromJust)
import Control.Monad.State
import Control.Monad.Except

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

-- | This is the class that offers the interface for unification. The user of
-- the library is not supposed to add instances to this class.
class (Substitutable a) => Unifiable a where
  {-# minimal unifyVal #-}
  unifyVal :: (Monad m) => Term a -> Term a -> UnificationT m (Term a)
  uni :: (Monad m) => Substitution -> Term a -> Term a -> UnificationT m (Term a)

instance {-# overlappable #-} Unifiable Int where
  unifyVal ta tb = do { st <- get; uni st ta tb }
  uni _ v@(Con a) (Con b)  | a == b     = pure v
                           | otherwise  = throwError IncompatibleUnification
  uni _ v@(Var i) (Var j)  | i == j     = pure v
  uni st (Var i) t         | isJust mbv = uni st (fromJust mbv) t
    where
      mbv = Subst.lookup @Int i st
  uni st (Var i) t         | otherwise  = bindv st i t
  uni st t       v@(Var _)              = uni st v t
  uni _ _ _                             = errorRecOnSimpleTypes

instance {-# overlappable #-} Unifiable Char where
  unifyVal ta tb = do { st <- get; uni st ta tb }
  uni _ v@(Con a) (Con b)  | a == b     = pure v
                           | otherwise  = throwError IncompatibleUnification
  uni _ v@(Var i) (Var j)  | i == j     = pure v
  uni st (Var i) t         | isJust mbv = uni st (fromJust mbv) t
    where
      mbv = Subst.lookup @Char i st
  uni st (Var i) t         | otherwise  = bindv st i t
  uni st t       v@(Var _)              = uni st v t
  uni _ _ _                             = errorRecOnSimpleTypes

instance {-# overlappable #-} Unifiable String where
  unifyVal ta tb = do { st <- get; uni st ta tb }
  uni _ v@(Con a) (Con b)  | a == b     = pure v
                           | otherwise  = throwError IncompatibleUnification
  uni _ v@(Var i) (Var j)  | i == j     = pure v
  uni st (Var i) t         | isJust mbv = uni st (fromJust mbv) t
    where
      mbv = Subst.lookup @String i st
  uni st (Var i) t         | otherwise  = bindv st i t
  uni st t       v@(Var _)              = uni st v t
  uni _ _ _                             = errorRecOnSimpleTypes

-- TODO: can I simplify these constraints?
instance {-# overlappable #-}
  forall a. (Typeable a, Show a, Eq a, Generic a, Substitutable a, HasDatatypeInfo a
          , All2 (Compose Show Term) (Code a)
          , All2 (Compose Eq Term) (Code a)
          , All2 (And Unifiable Substitutable) (Code a))
  => Unifiable a
  where
    unifyVal ta tb = do { st <- get; uni st ta tb }
    uni _ v@(Con a) (Con b)  | a == b     = pure v
                             | otherwise  = throwError IncompatibleUnification
    uni _ v@(Var i) (Var j)  | i == j     = pure v
    uni st (Var i) t         | isJust mbv = uni st (fromJust mbv) t
      where
        mbv = Subst.lookup @a i st
    uni st (Var i) t         | otherwise  = bindv st i t
    uni st t       v@(Var _)              = uni st v t
    uni _ (Rec t1) (Rec t2)
      | sameConstructor t1 t2 =
        let
          mt1   = hliftA  (Comp . Just) t1
          emt1  = hexpand (Comp Nothing) mt1
          pairs = hliftA2 unsafePair emt1 t2
        in do
          s <- hctraverse' (Proxy @(And Unifiable Substitutable))
                           (\(Comp (Pair s1 s2)) -> do
                               currSubst <- get
                               uni currSubst s1 s2)
                           pairs
          currSubst <- get
          pure $ currSubst @@ Rec s
      | otherwise = throwError IncompatibleUnification
    uni _ _ _ = throwError IncompatibleUnification

-- | This function binds an int to a term in a substitution. Intended for
-- private module use.
bindv
  :: forall m a. (Eq a, Eq (Term a), Show (Term a), Typeable a, Substitutable a, Monad m)
  => Substitution -> Int -> Term a -> UnificationT m (Term a)
bindv st i t = do
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
