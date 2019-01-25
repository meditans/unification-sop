--------------------------------------------------------------------------------
-- |
-- Module      :  Generic.Unification.Unification
-- Copyright   :  (C) 2018-19 Carlo Nucera
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Carlo Nucera <meditans@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module defines
--
--------------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Generic.Unification.Unification where

import Generics.SOP hiding (fromList)
import Data.Typeable
import Data.Maybe (isJust, fromJust)
import Control.Monad.State
import Control.Monad.Except

import Generic.Unification.Term
import Generic.Unification.Substitution

data UnificationError = IncompatibleUnification | OccursCheckFailed
  deriving (Show)

newtype Unification a
  = Unification
  { unUnification :: ExceptT UnificationError (State Substitution) a }
  deriving (Functor, Applicative, Monad, MonadState Substitution, MonadError UnificationError)

evalUnification :: Unification a -> Either UnificationError a
evalUnification a = evalState (runExceptT (unUnification a)) emptySubst

runUnification :: Unification a -> (Either UnificationError a, Substitution)
runUnification a = runState (runExceptT (unUnification a)) emptySubst

unify :: Unifiable a => a -> a -> Either UnificationError a
unify a b = evalUnification (unifyVal a b)

--------------------------------------------------------------------------------
-- Unifiable
--------------------------------------------------------------------------------

class Unifiable a where
  unifyVal :: a   -> a -> Unification a
  uni :: Substitution -> a -> a -> Unification a

instance {-# overlappable #-} Unifiable (Term Int) where
  unifyVal ta tb = do { st <- get; uni st ta tb }
  uni _ v@(Con a) (Con b)  | a == b     = pure v
                           | otherwise  = throwError IncompatibleUnification
  uni _ v@(Var i) (Var j)  | i == j     = pure v
  uni st (Var i) t         | isJust mbv = uni st (fromJust mbv) t
    where
      mbv = lookupSubst @Int i st
  uni st (Var i) t         | otherwise  = bindv st i t
  uni st t       v@(Var _)              = uni st v t
  uni _ _ _                             = errorRecOnSimpleTypes

instance {-# overlappable #-} Unifiable (Term Char) where
  unifyVal ta tb = do { st <- get; uni st ta tb }
  uni _ v@(Con a) (Con b)  | a == b     = pure v
                           | otherwise  = throwError IncompatibleUnification
  uni _ v@(Var i) (Var j)  | i == j     = pure v
  uni st (Var i) t         | isJust mbv = uni st (fromJust mbv) t
    where
      mbv = lookupSubst @Char i st
  uni st (Var i) t         | otherwise  = bindv st i t
  uni st t       v@(Var _)              = uni st v t
  uni _ _ _                             = errorRecOnSimpleTypes

instance {-# overlappable #-} Unifiable (Term String) where
  unifyVal ta tb = do { st <- get; uni st ta tb }
  uni _ v@(Con a) (Con b)  | a == b     = pure v
                           | otherwise  = throwError IncompatibleUnification
  uni _ v@(Var i) (Var j)  | i == j     = pure v
  uni st (Var i) t         | isJust mbv = uni st (fromJust mbv) t
    where
      mbv = lookupSubst @String i st
  uni st (Var i) t         | otherwise  = bindv st i t
  uni st t       v@(Var _)              = uni st v t
  uni _ _ _                             = errorRecOnSimpleTypes

instance {-# overlappable #-}
  forall a. (Typeable a, Show a, Eq a, Generic a, Substitutable (Term a), HasDatatypeInfo a
          , All2 (Compose Show Term) (Code a)
          , All2 (Compose Eq Term) (Code a)
          , All2 (And (Compose Unifiable Term) (Compose Substitutable Term)) (Code a))
  => Unifiable (Term a)
  where
    unifyVal ta tb = do { st <- get; uni st ta tb }
    uni _ v@(Con a) (Con b)  | a == b     = pure v
                             | otherwise  = throwError IncompatibleUnification
    uni _ v@(Var i) (Var j)  | i == j     = pure v
    uni st (Var i) t         | isJust mbv = uni st (fromJust mbv) t
      where
        mbv = lookupSubst @a i st
    uni st (Var i) t         | otherwise  = bindv st i t
    uni st t       v@(Var _)              = uni st v t
    uni _ (Rec t1) (Rec t2)
      | sameConstructor t1 t2 =
        let
          mt1   = hliftA  (Comp . Just) t1
          emt1  = hexpand (Comp Nothing) mt1
          pairs = hliftA2 unsafePair emt1 t2
        in do
          s <- hctraverse' (Proxy @(And (Compose Unifiable Term)
                                   (Compose Substitutable Term)))
                           (\(Comp (Pair s1 s2)) -> do
                               currSubst <- get
                               uni currSubst s1 s2)
                           pairs
          currSubst <- get
          pure $ currSubst @@ Rec s
      | otherwise = throwError IncompatibleUnification
    uni _ _ _ = throwError IncompatibleUnification

bindv
  :: forall a. (Eq a, Eq (Term a), Show (Term a), Typeable a, Substitutable (Term a))
  => Substitution -> Int -> Term a -> Unification (Term a)
bindv st i t = do
  put (singletonSubst i t @@ st)
  pure t

-- >>> unify ex5' ex5'
-- Right (fooS (Con "ciao") (fooS (Var 1) (Con (FooI 2))))
-- >>> evalUnification $ unifyVal ex5' ex5'var
-- Right (fooS (Con "ciao") (fooS (Con "hey") (Con (FooI 2))))
-- >>> evalUnification $ unifyVal ex5' ex5'var2
-- Left IncompatibleUnification

-- Let's do an example with lists: I need the smart constructors
nil :: Term [a]
nil = Con []

cons :: Term a -> Term [a] -> Term [a]
cons t ts = Rec . SOP . S . Z $ t :* ts :* Nil

ex_list1_1, ex_list1_2, ex_list1_3 :: Term [Int]
ex_list1_1 = cons (Var 1)   (cons (Var 2) nil)
ex_list1_2 = cons (Var 2)   (cons (Var 1) nil)
ex_list1_3 = cons (Con 100) (cons (Var 3) nil)

-- >>> runUnification $ unifyVal ex_list1_1 ex_list1_2
-- (Right (: (Var 1) (: (Var 1) (Con []))),Substitution { Int -> [(1,Var 2),(2,Var 1)] })

-- >>> ex_list1_1 `unify` ex_list1_2 >>= (`unify` ex_list1_3)
-- Right (: (Con 100) (: (Con 100) (Con [])))

-- Let's see an example with an infinite solution, the prolog [a, X] = X

ex_list2_1, ex_list2_2, ex_list2_3 :: Term [Int]
ex_list2_1 = cons (Con 1) (Var 1)
ex_list2_2 = Var 1
ex_list2_3 = cons (Var 2) (cons (Var 3) (Var 4))

-- >>> runUnification (unifyVal ex_list2_1 ex_list2_2)
-- (Right (: (Con 1) (Var 1)),Substitution { [Int] -> [(1,: (Con 1) (Var 1))] })

-- >>> runUnification (unifyVal ex_list2_2 ex_list2_1)
-- (Right (: (Con 1) (Var 1)),Substitution { [Int] -> [(1,: (Con 1) (Var 1))] })

-- >>> unify ex_list2_1 ex_list2_2 >>= unify ex_list2_3
-- Right (: (Con 1) (: (Var 3) (Var 4)))
-- >>> unify ex_list2_1 ex_list2_3 >>= unify ex_list2_2
-- Right (: (Con 1) (: (Var 3) (Var 4)))
-- >>> unify ex_list2_2 ex_list2_3 >>= unify ex_list2_1
-- Right (: (Con 1) (: (Var 3) (Var 4)))

-- >>> runUnification $ unifyVal ex_list2_1 ex_list2_2 >>= unifyVal ex_list2_3
-- (Right (: (Con 1) (: (Con 1) (: (Con 1) (: (Con 1) (: (Con 1) (Var 1)))))),Substitution { [Int] -> [(1,: (Con 1) (Var 1)),(4,: (Con 1) (Var 1))], Int -> [(2,Con 1),(3,Con 1)] })
-- >>> runUnification $ unifyVal ex_list2_1 ex_list2_3 >>= unifyVal ex_list2_2
-- (Right (: (Con 1) (: (Con 1) (: (Var 3) (Var 4)))),Substitution { [Int] -> [(1,: (Var 3) (Var 4)),(4,: (Var 3) (Var 4))], Int -> [(2,Con 1),(3,Con 1)] })
-- >>> runUnification $ unifyVal ex_list2_2 ex_list2_3 >>= unifyVal ex_list2_1
-- (Right (: (Con 1) (: (Con 1) (: (Con 1) (: (Con 1) (: (Var 3) (Var 4)))))),Substitution { [Int] -> [(1,: (Var 2) (: (Var 3) (Var 4))),(4,: (Var 3) (Var 4))], Int -> [(2,Con 1),(3,Con 1)] })

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

data Pair a = Pair a a

unsafePair :: forall a. (:.:) Maybe Term a -> Term a -> (Pair :.: Term) a
unsafePair (Comp (Just t1)) t2 = Comp $ Pair t1 t2
unsafePair (Comp Nothing)   _  = error "Structures should be matched"

sameConstructor :: SOP a b -> SOP a b -> Bool
sameConstructor a b = hindex a == hindex b