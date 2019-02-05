-- | Following the paper "Prolog control constructs in a functional setting" by
-- Hinze, because I only want a clear denotational semantic for now. This is
-- done as an experiment, and will not be part of the final package.

{-# LANGUAGE DeriveGeneric, DerivingStrategies, DerivingVia   #-}
{-# LANGUAGE ExistentialQuantification, FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving    #-}
{-# LANGUAGE MultiParamTypeClasses, RankNTypes, TupleSections #-}
{-# LANGUAGE UndecidableInstances                             #-}

module Generic.Unification.Hinze
  ( Backtr (..)
  , Cut (..)
  , naf, naf2, only
  , BacktrT (..)
  , CutT (..)
  , Logic (..)
  , runLogic, evalLogic, (===)
  ) where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Data.Either (rights)
import Data.Maybe  (listToMaybe)
import Generics.SOP
import qualified GHC.Generics as GHC

import Generic.Unification.Term
import Generic.Unification.Unification
import Generic.Unification.Substitution

--------------------------------------------------------------------------------
-- Implementation, following Hinze
--------------------------------------------------------------------------------

-- | Important classes

class (Monad m) => Backtr m where
  -- | No solutions, corresponds to fail in prolog
  flop :: m a
  -- | Non-deterministing choice between two branches
  amb  :: m a -> m a -> m a
  -- | Encapsulation, find one solution
  once :: m a -> m (Maybe a)
  -- | Encapsulation, find all solutions
  sols :: m a -> m [a]

class (Backtr m) => Cut m where
  -- | like in prolog, cut discards choicepoints
  cut  :: m ()
  -- | to delimit the effect of a cut in a region
  call :: m a -> m a

--------------------------------------------------------------------------------
-- Interesting operations with the classes
--------------------------------------------------------------------------------

-- | Negation as failure
naf :: Backtr m => m a -> m ()
naf m = once m >>= maybe true (\_ -> flop)

-- | Subtly different negation as failure
naf2 :: Cut m => m a -> m ()
naf2 m = call ((m >> cut >> flop) `amb` true)

-- | Equivalent to once/1 in prolog. Note, the once function in the typeclass is
-- the encapsulated version of this operation.
only :: (Cut m) => a -> m a
only a = cut >> pure a

--------------------------------------------------------------------------------
-- Auxiliary definitions
--------------------------------------------------------------------------------

class MonadT t where
  up   :: (Monad m) => m a -> t m a
  down :: (Monad m) => t m a -> m a

type CPS a ans = (a -> ans) -> ans

data Answer m a = No | Yes a (m (Answer m a))

--------------------------------------------------------------------------------
-- The BacktrT monad
--------------------------------------------------------------------------------

newtype BacktrT m a = BacktrT { (>>-) :: forall ans. CPS a (m ans -> m ans) }

instance Functor (BacktrT m) where
  fmap f g = BacktrT $ \h ->
    g >>- \a -> h (f a)

instance Applicative (BacktrT m) where
  pure a = BacktrT $ \k -> k a
  cf <*> ca = BacktrT $ \k ->
    cf >>- \f ->
    ca >>- \a ->
    k (f a)

instance Monad (BacktrT m) where
  return   = pure
  ca >>= f = BacktrT $ \k ->
    ca  >>- \a  ->
    f a >>- \fa ->
    k fa

instance MonadT BacktrT where
  up m             = BacktrT $ \k f -> m >>= \a -> k a f
  down (BacktrT m) = m (\a _ -> pure a) (error "no solution")

instance (Monad m) => Backtr (BacktrT m) where
  flop      = BacktrT $ \_ -> id
  (BacktrT m) `amb` (BacktrT n) = BacktrT $ \k -> m k . n k
  once (BacktrT m) = up (m just nothing)
  sols (BacktrT m) = up (m cons nil)

--------------------------------------------------------------------------------
-- The CutT monad
--------------------------------------------------------------------------------

newtype CutT m a = CutT { (>>--) :: forall ans. CPS a (m (Answer m ans) -> m (Answer m ans)) }

instance Functor (CutT m) where
  fmap f g = CutT $ \h ->
    g >>-- \a -> h (f a)

instance Applicative (CutT m) where
  pure a = CutT $ \k -> k a
  cf <*> ca = CutT $ \k ->
    cf >>-- \f ->
    ca >>-- \a ->
    k (f a)

instance Monad (CutT m) where
  return   = pure
  ca >>= f = CutT $ \k ->
    ca  >>-- \a  ->
    f a >>-- \fa ->
    k fa

instance MonadT CutT where
  up m = CutT $ \k f -> m >>= \a -> k a f
  down (CutT m) = m yes no >>= answer (error "no solution!") (\a _ -> pure a)

instance (Monad m) => Backtr (CutT m) where
  flop = CutT $ \_ -> id
  (CutT m) `amb` (CutT n) = CutT $ \k -> m k . n k
  once (CutT m) = up (m yes no >>= answer nothing just)
  sols (CutT m) = up (m yes no >>= answer nil cons)

instance (Monad m) => Cut (CutT m) where
  cut = CutT $ \k _ -> k () no
  call (CutT m) = CutT $ \k f -> m yes no >>= answer f k

--------------------------------------------------------------------------------
-- Lifting of Backtr and Cut instances over ExceptT and StateT
--------------------------------------------------------------------------------

instance Backtr m => Backtr (ExceptT e m) where
  flop = ExceptT flop
  (ExceptT t1) `amb` (ExceptT t2) = ExceptT $ t1 `amb` t2
  once (ExceptT t) = ExceptT (fmap (Right . listToMaybe . rights) $ sols t)
  sols (ExceptT t) = ExceptT (fmap (Right .               rights) $ sols t)

instance Backtr m => Backtr (StateT s m) where
  flop = StateT (\_ -> flop)
  (StateT a) `amb` (StateT b) = StateT $ \s -> a s `amb` b s
  once (StateT a) = StateT $ \s -> fmap ((,s) . fmap fst) . once $ a s
  sols (StateT t) = StateT $ \s -> fmap ((,s) . fmap fst) . sols $ t s

instance Cut m => Cut (ExceptT e m) where
  cut  = ExceptT $ fmap Right cut
  call (ExceptT t) = ExceptT (call t)

instance Cut m => Cut (StateT s m) where
  cut = StateT $ \s -> fmap (,s) cut
  call (StateT t) = StateT $ \s -> call (t s)

--------------------------------------------------------------------------------
-- Logic, directly using UnificationT
--------------------------------------------------------------------------------

-- this is morally s -> m [Either e (a, s)]
newtype Logic a = Logic { unLogic :: UnificationT (CutT Identity) a }
  deriving (Functor, Applicative, Monad, Backtr, Cut, MonadState Substitution, MonadError UnificationError)
    via StateT Substitution (ExceptT UnificationError (CutT Identity))

runLogic :: Logic a -> [Either UnificationError (a, Substitution)]
runLogic = runIdentity . down . sols . flip runUnificationT mempty . unLogic

evalLogic :: Logic a -> [a]
evalLogic = runIdentity . fmap (Prelude.map fst . rights) . down . sols . flip runUnificationT mempty . unLogic

(===) :: Unifiable a => Term a -> Term a -> Logic (Term a)
a === b = Logic (unify a b)

--------------------------------------------------------------------------------
-- Member, logical style
--------------------------------------------------------------------------------

data Pair a = Pair a a deriving (Show, Eq, GHC.Generic)
instance Generic (Pair a) where
instance HasDatatypeInfo (Pair a) where

pair :: Term a -> Term a -> Term (Pair a)
pair a b = Rec . SOP . Z $ a :* b :* Nil

key :: Term (Pair Int)
key = pair (Con 1) (Var 1)

dict :: [Term (Pair Int)]
dict =
  [ pair (Con 1) (Con 2)
  , pair (Con 2) (Con 3)
  , pair (Con 1) (Con 4)
  ]

-- member(X, [X|Y]).
-- member(X, [_|Y]) :- member(X,Y).

memb :: (Unifiable a) => Term a -> [Term a] -> Logic (Term a)
memb _ []     = flop
memb a (b:bs) = a === b `amb` memb a bs

-- >>> runLogic $ memb key dict
-- [ Right (pair (Con 1) (Con 2),Substitution { Int -> [(1,Con 2)] })
-- , Left IncompatibleUnification
-- , Right (pair (Con 1) (Con 4),Substitution { Int -> [(1,Con 4)] })]

-- >>> evalLogic $ memb key dict
-- [ pair (Con 1) (Con 2) , pair (Con 1) (Con 4) ]

-- >>> runLogic $ memb (pair (Var 1) (Var 2)) dict
-- [ Right (pair (Con 1) (Con 2),Substitution { Int -> [(1,Con 1),(2,Con 2)] })
-- , Right (pair (Con 2) (Con 3),Substitution { Int -> [(1,Con 2),(2,Con 3)] })
-- , Right (pair (Con 1) (Con 4),Substitution { Int -> [(1,Con 1),(2,Con 4)] })]

--------------------------------------------------------------------------------
-- Example from the paper
--------------------------------------------------------------------------------

child :: String -> Logic String
child "terach"  = pure "abraham" `amb` pure "nachor" `amb` pure "haran"
child "abraham" = pure "isaac"
child "haran"   = pure "lot" `amb` pure "milcah" `amb` pure "yiscah"
child "sarah"   = pure "isaac"
child _         = flop

grandChild :: String -> Logic String
grandChild = child >=> child

-- >>> evalLogic $ child "terach"
-- [ "abraham" , "nachor" , "haran" ]

-- >>> evalLogic $ grandChild "terach"
-- [ "isaac" , "lot" , "milcah" , "yiscah" ]

-- >>> take 2 . evalLogic $ grandChild "terach"
-- [ "isaac" , "lot" ]

-- >>> evalLogic $ child "isaac"
-- []

-- >>> evalLogic $ once (child "isaac")
-- [ Nothing ]

--------------------------------------------------------------------------------
-- Appendix, lifted values for convenience
--------------------------------------------------------------------------------

true :: Monad m => m ()
true = pure ()

just :: (Monad m) => a -> m (Maybe a) -> m (Maybe a)
just a _ = pure (Just a)

nothing :: (Monad m) => m (Maybe a)
nothing = pure Nothing

nil :: (Monad m) => m [a]
nil = pure []

cons :: (Monad m) => a -> m [a] -> m [a]
cons a ms = do
  as <- ms
  pure (a : as)

answer :: (Monad m) => m b -> (a -> m b -> m b) -> Answer m a -> m b
answer n _ No = n
answer n y (Yes a m) = y a (m >>= answer n y)

yes :: (Monad m) => a -> m (Answer m a) -> m (Answer m a)
yes a mA = pure (Yes a mA)

no :: (Monad m) => m (Answer m a)
no = pure No
