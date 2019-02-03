-- | This module is experimental, for me to play with the interface of
-- unification. Will not be present in the final release.

{-# language DeriveGeneric, GeneralizedNewtypeDeriving, DataKinds, KindSignatures, ExistentialQuantification #-}

module Generic.Unification.Prolog where

import Generic.Unification.Term
import Generic.Unification.Substitution
import Generic.Unification.Unification
import Control.Monad.Logic
import qualified GHC.Generics as GHC
import Generics.SOP
import Control.Applicative

newtype Prolog a = Prolog {unProlog :: LogicT Unification a}
  deriving (Functor, Applicative, Monad, Alternative, MonadPlus, MonadLogic)

runProlog :: Prolog a -> Either UnificationError [a]
runProlog = evalUnification . observeAllT . unProlog

data Pair a = Pair a a deriving (Eq, Show, GHC.Generic)

instance Generic (Pair a)

-- Ho (1,X) e una lista [(0,1), (0,2), (1,2), (1,3), (2,3), (2,4)] e voglio
-- vedere con chi unifica.

pair :: Term a -> Term b -> Term (a,b)
pair ta tb = Rec . SOP . Z $ ta :* tb :* Nil

ex1 :: Term (Int, Int)
ex1 = pair (Con 1) (Var 1)

ex2, ex2' :: Term (Int, Int)
ex2  = pair (Con 1) (Con 2)
ex2' = Con (1,2)

-- TODO PROBLEM! These two should yield the same result!
-- >>> unify ex1 ex2
-- Right ((,) (Con 1) (Con 2))
-- >>> unify ex1 ex2'
-- Left IncompatibleUnification

selectSimple = do
  let
    a :: Term (Int, Int)
    a = ex1
    dict :: [Term (Int, Int)]
    dict = [pair (Con x) (Con y) | x <- [1,2,3], y <- [1,2,3]]
  b <- dict
  guard (isRight $ unify a b)
  return b

isRight (Right _) = True
isRight (Left  _) = False

nil :: Term [a]
nil = Con []

cons :: Term a -> Term [a] -> Term [a]
cons ta tas = Rec . SOP . S . Z $ ta :* tas :* Nil

liftOneLevel :: [Term a] -> Term [a]
liftOneLevel = foldr cons nil

--------------------------------------------------------------------------------
-- Propositions
--------------------------------------------------------------------------------

data Pattern   (as :: [*]) = Pattern String (NP Term as)
data DefClause (as :: [*]) = NP Term as :- [WrappedProp]
type Prop (as :: [*]) = [DefClause as]

data WrappedProp = forall as. WrappedProp (DefClause as)
-- This is Wrong ^


-- This expresses prolog's
-- 
-- member(X, [X|Y])
-- member(X, [_|Y]) :- member(X,Y)
-- 
memberP1 :: Prop '[ Int, [Int] ]
memberP1 =
  [ (Var 1 :* (cons (Var 1) (Var 2)) :* Nil) :- []
  , (Var 1 :* (cons (Var 2) (Var 3)) :* Nil) :- [WrappedProp undefined]
  ]


-- or I could reify all things:
data Member a = Member a [a]
-- and so a Term (Member a) could be a

exMember :: Term (Member a)
exMember = Rec undefined

-- But then, what's a list of goals?