-- | Following the paper "Prolog control constructs in a functional setting" by
-- Hinze, because I only want a clear denotational semantic for now. This is
-- done as an experiment, and will not be part of the final package.

{-# LANGUAGE ExistentialQuantification, RankNTypes, FlexibleInstances, UndecidableInstances, FlexibleContexts, DeriveGeneric, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}

module Generic.Unification.Hinze where

import Prelude hiding (fail)
import Control.Monad hiding (fail)
import Control.Monad.Identity hiding (fail)
import qualified GHC.Generics as GHC
import Generics.SOP
import Control.Monad.Error hiding (fail)
import Control.Monad.Trans
import Control.Monad.State hiding (fail)

import Generic.Unification.Term
import Generic.Unification.Unification
import Generic.Unification.Substitution

-- | Important classes

class (Monad m) => Backtr m where
  fail :: m a
  amb  :: m a -> m a -> m a
  once :: m a -> m (Maybe a)
  sols :: m a -> m [a]

true :: Monad m => m ()
true = pure ()

-- | Negation as failure
naf :: (Backtr m) => m a -> m ()
naf m = once m >>= maybe true (\_ -> fail)

class (Backtr m) => Cut m where
  cut  :: m ()
  call :: m a -> m a -- to delimit the effect of a cut

only :: (Cut m) => a -> m a
only a = cut >> pure a

naf2 :: Cut m => m a -> m ()  -- subtly different from naf
naf2 m = call ((m >> cut >> fail) `amb` true) -- cut/fail

child :: (Backtr m) => String -> m String
child "terach"  = pure "abraham" `amb` pure "nachor" `amb` pure "haran"
child "abraham" = pure "isaac"
child "haran"   = pure "lot" `amb` pure "milcah" `amb` pure "yiscah"
child "sarah"   = pure "isaac"
child _         = fail

grandChild :: (Backtr m) => String -> m String
grandChild = child >=> child

class MonadT t where
  up   :: (Monad m) => m a -> t m a
  down :: (Monad m) => t m a -> m a

type CPS a ans = (a -> ans) -> ans
newtype BacktrT m a = BacktrT { (>>-) :: forall ans. CPS a (m ans -> m ans) }

-- >>- :: BacktrT m a -> (a -> ans) -> ans

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
  fail      = BacktrT $ \k -> id
  (BacktrT m) `amb` (BacktrT n) = BacktrT $ \k -> m k . n k
  once (BacktrT m) = up (m first nothing)
  sols (BacktrT m) = up (m cons nil)

nothing :: (Monad m) => m (Maybe a)
nothing = pure Nothing

nil :: (Monad m) => m [a]
nil = pure []

cons :: (Monad m) => a -> m [a] -> m [a]
cons a ms = do
  as <- ms
  pure (a : as)

first :: (Monad m) => a -> m (Maybe a) -> m (Maybe a)
first a _ = pure (Just a)

data Answer m a = No
                | Yes a (m (Answer m a))

answer :: (Monad m) => m b -> (a -> m b -> m b) -> Answer m a -> m b
answer no yes No = no
answer no yes (Yes a m) = yes a (m >>= answer no yes)

no :: (Monad m) => m (Answer m a)
no = pure No
yes :: (Monad m) => a -> m (Answer m a) -> m (Answer m a)
yes a mA = pure (Yes a mA)

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
  fail = CutT $ \k -> id
  (CutT m) `amb` (CutT n) = CutT $ \k -> m k . n k
  once (CutT m) = up (m yes no >>= answer nothing first)
  sols (CutT m) = up (m yes no >>= answer nil cons)

instance (Monad m) => Cut (CutT m) where
  cut = CutT $ \k f -> k () no
  call (CutT m) = CutT $ \k f -> m yes no >>= answer f k

class (Monad m) => Run m where
  run :: m a -> a

instance (MonadT t, Run m, Monad (t m)) => Run (t m) where
  run = run . down

instance Run Identity where
  run (Identity a) = a

runB :: BacktrT Identity a -> a
runB = run

-- >>> run $ sols (child "terach" :: BacktrT Identity String)
-- [ "abraham" , "nachor" , "haran" ]
-- >>> run $ sols (grandChild "terach" :: BacktrT Identity String)
-- [ "isaac" , "lot" , "milcah" , "yiscah" ]
-- >>> take 2 . run $ sols (grandChild "terach" :: BacktrT Identity String)
-- [ "isaac" , "lot" ]
-- >>> run $ (child "isaac" :: BacktrT Identity String)
-- *** Exception: no solution
-- CallStack (from HasCallStack):
--   error, called at /home/carlo/code/haskell/unification-sop/src/Generic/Unification/Hinze.hs:77:42 in unification-sop-0.1.0.0-inplace:Generic.Unification.Hinze
-- >>> run $ once (child "isaac" :: BacktrT Identity String)
-- Nothing

-- I could wrap a state monad transformer inside to carry the substitutions and
-- the counter for the fresh variables, and then cook up a way to talk about
-- attributed variables, which is not too expensive computationally.
--

-- How would member be implemented here? The point is that without unification
-- member is pointless, because I could just use a haskell function. But, when I
-- have unification, stating member is a constraint that has to be satisfied,
-- and so composes in greater logical programs.

-- This lifts unification on terms to a monadic action in backtrackable monads
unifyB :: (Unifiable (Term a), Backtr m) => Term a -> Term a -> m (Term a)
unifyB t1 t2 = either (const fail) pure $ unify t1 t2

-- ("a", X) `member` [("a", "b"), ("b", "c")]
memb :: (Unifiable (Term a), Backtr m) => Term a -> [Term a] -> m (Term a)
memb a []     = fail
memb a (b:bs) = unifyB a b `amb` memb a bs

memb2 :: (Unifiable (Term a)) => Term a -> [Term a] -> Logic (Term a)
memb2 a []     = fail
memb2 a (b:bs) = a === b `amb` memb2 a bs

memb3 :: (Unifiable (Term a)) => Term a -> [Term a] -> Logic (Term a, Substitution)
memb3 a []     = fail
memb3 a (b:bs) = (do n <- a === b; s <- get; pure (n, s) ) `amb` memb3 a bs

(===) :: Unifiable a => a -> a -> Logic a
a === b = Logic $ lift (unifyVal a b)


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

-- >>> runB $ do a <- sols $ memb key dict ; return (a, key)
-- ( [ pair (Con 1) (Con 2) , pair (Con 1) (Con 4) ]
-- , pair (Con 1) (Var 1)
-- )
--

-- But this ^ is not what I have in mind, because it resets the substitutions
-- every time. Instead I want the substitutions to be maintained.
--

--------------------------------------------------------------------------------
-- Modern style
--------------------------------------------------------------------------------

instance MonadTrans CutT where
  lift m = CutT $ \k f -> m >>= \a -> k a f

instance MonadState s m => MonadState s (CutT m) where
  get   = lift get
  put   = lift . put
  state = lift . state

newtype Logic a = Logic { unLogic :: CutT Unification a }
  deriving (Functor, Applicative, Monad, Backtr, Cut, MonadState Substitution)

evalLogic :: Logic a -> [a]
evalLogic = either (const []) id . evalUnification . down . sols . unLogic

-- runLogic :: Logic a -> _
runLogic :: Logic a -> Either UnificationError ([a], Substitution)
runLogic = runUnification . down . sols . unLogic

-- >>> runLogic $ memb key dict
-- Right
--   ( [ pair (Con 1) (Con 2) , pair (Con 1) (Con 4) ]
--   , Substitution {}
--   )
-- >>> evalLogic $ memb key dict
-- [ pair (Con 1) (Con 2) , pair (Con 1) (Con 4) ]
-- >>> runLogic $ memb2 key dict
-- Left IncompatibleUnification
-- >>> evalLogic $ memb2 key dict
-- []

-- The substitution contains the last used substitution:

-- >>> runLogic $ memb2 (pair (Var 1) (Var 2)) dict
-- Left IncompatibleUnification
