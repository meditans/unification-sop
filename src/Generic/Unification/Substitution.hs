--------------------------------------------------------------------------------
-- |
-- Module      :  Generic.Unification.Substitution
-- Copyright   :  (C) 2018-19 Carlo Nucera
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Carlo Nucera <meditans@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module defines
--
--------------------------------------------------------------------------------

{-# language RankNTypes, TypeApplications, DerivingVia, KindSignatures, TypeOperators, ScopedTypeVariables, PolyKinds, FlexibleInstances, FlexibleContexts, UndecidableInstances, ConstraintKinds, GADTs, AllowAmbiguousTypes #-}

module Generic.Unification.Substitution where

import Generics.SOP hiding (fromList)
import Data.Typeable
import qualified Data.TypeRepMap as TM
import qualified Data.IntMap     as IM
import GHC.Base (Type, coerce)
import qualified Type.Reflection as TR
import Data.List (intercalate)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Data.Functor.Const
import GHC.Exts (toList)

import Generic.Unification.Term

--------------------------------------------------------------------------------
-- Substitutions
--------------------------------------------------------------------------------

-- So our substitution should be a map from VarRep to Terms of that type! Maybe
-- we could use the indexed versions of TypeRep. At that point, the map would be

data Constrained c f a = c a => Constrained (f a)

withConstrained :: (forall x. c x => f x -> r) -> Constrained c f a -> r
withConstrained f (Constrained fa) = f fa

-- Questo non va bene perche' non puo' essere applicato parzialmente.
-- type WellFormed a = (Show (Term a), Substitutable (Term a))
class    (Eq a, Eq (Term a), Show (Term a), Substitutable (Term a)) => WellFormed (a :: Type) where
instance (Eq a, Eq (Term a), Show (Term a), Substitutable (Term a)) => WellFormed a where

newtype Substitution = Substitution (TM.TypeRepMap (Constrained WellFormed (IM.IntMap :.: Term)))

-- Now, convenient operation to insert something
emptySubst :: Substitution
emptySubst = Substitution TM.empty

insertSubst
  :: forall a. (WellFormed a, Typeable a)
  => Int -> Term a -> Substitution -> Substitution
insertSubst i ta (Substitution subst) =
  case TM.member @a subst of
    True  -> Substitution $ TM.adjust @a (\(Constrained (Comp m)) -> Constrained $ Comp (IM.insert i ta m)) subst
    False -> Substitution $ TM.insert @a (Constrained . Comp $ IM.singleton i ta) subst

singletonSubst :: forall a. (WellFormed a, Typeable a) => Int -> Term a -> Substitution
singletonSubst i t = insertSubst i t emptySubst

ex_substitution :: Substitution
ex_substitution = insertSubst @Char 1 (Con 'c') $ insertSubst @Int 1 (Con 1000) emptySubst
ex_substitution2 :: Substitution
ex_substitution2 = insertSubst @Foo 1 ex5' emptySubst

-- >>> ex_substitution
-- Substitution { Int -> fromList [(1,Con 1000)], Char -> fromList [(1,Con 'c')] }

lookupSubst :: forall a. (Typeable a) => Int -> Substitution -> Maybe (Term a)
lookupSubst i (Substitution subst) = do
  Constrained (Comp internalMap) <- TM.lookup @a subst
  IM.lookup i internalMap

-- lookupSubst' :: forall (k :: Type) a. (Typeable a) => TR.TypeRep k -> Int -> Substitution -> Maybe (Term a)
-- lookupSubst' tr i s = TR.withTypeable @Type tr (lookupSubst i s)

  -- Constrained (Comp internalMap) <- TM.lookup @a subst
  -- IM.lookup i internalMap

-- I also have to implement union of substitutions, with the same bias of those
-- in Data.Map I expect, which means that I prefer things that exists in the
-- first map if a collision should arise, because I want to use this definition
-- for the composition of substitutions.

-- I expect to piggyback on the definition of union for the separate maps, with
-- this provision though: if I find an exsting map for a type, this doesn't mean
-- that I should substitute the entirety of the second map, at the place: for
-- example, if I find [Int -> map1, String -> map2] as the first map, and [Int
-- -> map3] as the second one, then I have a collision in the Int, and I should
-- not simply take the first map alltogether. Instead I should do the unions of
-- the inside maps. Recapitulating, I have to do a unionWith on the Type map,
-- and a simple union on the term level map.

unionSubst :: Substitution -> Substitution -> Substitution
unionSubst (Substitution s1) (Substitution s2) = Substitution $ TM.unionWith union' s1 s2
  where
    union' :: Constrained WellFormed (IM.IntMap :.: Term) a
           -> Constrained WellFormed (IM.IntMap :.: Term) a
           -> Constrained WellFormed (IM.IntMap :.: Term) a
    union' (Constrained (Comp m1)) (Constrained (Comp m2))  = Constrained $ Comp (IM.union m1 m2)

mapSubst :: (forall x. WellFormed x => Term x -> Term x) -> Substitution -> Substitution
mapSubst f (Substitution s) = Substitution $ TM.hoist help1 s
  where
    help1 :: Constrained WellFormed (IM.IntMap :.: Term) x
          -> Constrained WellFormed (IM.IntMap :.: Term) x
    help1 (Constrained (Comp a)) = Constrained . Comp $ IM.map f a

-- >>> :set -XTypeApplications
-- >>> unionSubst (GenericPrologTermUniqueType.insert @Int 1 (Con 1) empty) (GenericPrologTermUniqueType.insert @Int 1 (Con 2) empty)
-- TypeRepMap [ Int ]

-- Unfortunately the show representation that is given here doesn't let us see
-- the actual content. Let us write a better show function instead:
--
-- It seems that I can get the keys, so all I have to do now is do a lookup for
-- every SomeTypeRep into the map. But how can I do that? Note that using toList
-- ends with a segmentation fault. I'm now trying to write a new show instance
-- by myself. The major problem being that I cannot search given a key, because:

-- 1) keys returns [SomeTypeRep]
-- 2) lookup :: forall a f. Typeable a => TypeRepMap f -> Maybe (f a)

-- So basically there is no way to signal how we want the typeable. Unless we
-- could wrap this in another function like:

lookupTM :: forall k (a :: k) f. Typeable a => TR.TypeRep a -> TM.TypeRepMap f -> Maybe (f a)
lookupTM _ = TM.lookup

instance Show Substitution where
  show (Substitution s) = wrap . intercalate ", " . map showInner $ toList s
    where
      showInner :: TM.WrapTypeable (Constrained WellFormed (IM.IntMap :.: Term)) -> String
      showInner (TM.WrapTypeable a@(Constrained (Comp im))) =
        show (typeRep a) ++ " -> " ++ show (toList im)
      wrap a = "Substitution { "  ++ a ++ " }"

-- >>> :set -XTypeApplications
-- >>> ex_substitution
-- Substitution { Int -> [(1,Con 1000)], Char -> [(1,Con 'c')] }

--------------------------------------------------------------------------------
-- Unification
--------------------------------------------------------------------------------

newtype FreeVars = FreeVars (TM.TypeRepMap (Const IntSet :: Type -> Type))

instance Semigroup FreeVars where
  (FreeVars xs) <> (FreeVars ys) = FreeVars $ TM.unionWith setUnion xs ys
    where
      setUnion :: Const IntSet x -> Const IntSet x -> Const IntSet x
      setUnion (Const s1) (Const s2) = Const $ IS.union s1 s2

instance Monoid FreeVars where
  mempty  = FreeVars TM.empty
  mappend = (<>)

instance Show FreeVars where
  show (FreeVars s) = wrap . intercalate ", " . map showInner $ toList s
    where
      showInner (TM.WrapTypeable a@(Const is)) =
        show (typeRep a) ++ " -> " ++ show (toList is)
      wrap a = "FreeVars { "  ++ a ++ " }"

memberFreeVars :: forall (a :: Type). (Typeable a) => Int -> FreeVars -> Bool
memberFreeVars i (FreeVars tm) =
  case TM.lookup @a tm of
    Just (Const is) -> IS.member i is
    Nothing -> False

-- And a synonym for visited sets

newtype Visited = Visited (TM.TypeRepMap (Const IntSet :: Type -> Type))
  deriving (Semigroup, Monoid) via FreeVars

instance Show Visited where
  show (Visited s) = wrap . intercalate ", " . map showInner $ toList s
    where
      showInner (TM.WrapTypeable a@(Const is)) =
        show (typeRep a) ++ " -> " ++ show (toList is)
      wrap a = "Visited { "  ++ a ++ " }"

-- Searching in a visited set is the same as searching in the free variables
memberVisited :: forall (a :: Type). (Typeable a) => Int -> Visited -> Bool
memberVisited = coerce (memberFreeVars @a)

insertVisited :: forall (a :: Type). (Typeable a) => Int -> Visited -> Visited
insertVisited i (Visited tm) =
  Visited $ TM.unionWith
              (\(Const is1) (Const is2) -> Const (IS.union is1 is2))
              (TM.one @a . Const $ IS.singleton i)
              tm

--------------------------------------------------------------------------------
-- Substitutable
--------------------------------------------------------------------------------

class Substitutable a where
  -- TODO: decide an interface for @@ vs sbs
  (@@) :: Substitution -> a -> a
  ftv  :: a -> FreeVars
  sbs  :: Visited -> Substitution -> a -> a

instance {-# overlaps #-} Substitutable (Term Int) where
  -- TODO: decide an interface for @@ vs sbs
  s @@ (Var i) = maybe (Var i) id (lookupSubst i s)
  _ @@ (Con i) = Con i
  _ @@ (Rec _) = errorRecOnSimpleTypes
  ftv (Var i)  = FreeVars $ TM.one @Int (Const $ IS.singleton i)
  ftv (Con _)  = FreeVars $ TM.empty
  ftv (Rec _)  = errorRecOnSimpleTypes
  sbs = undefined

instance {-# overlaps #-} Substitutable (Term Char) where
  -- TODO: decide an interface for @@ vs sbs
  s @@ (Var i) = maybe (Var i) id (lookupSubst i s)
  _ @@ (Con c) = Con c
  _ @@ (Rec _) = errorRecOnSimpleTypes
  ftv (Var i)  = FreeVars $ TM.one @Int (Const $ IS.singleton i)
  ftv (Con _)  = FreeVars $ TM.empty
  ftv (Rec _)  = errorRecOnSimpleTypes
  sbs = undefined

instance {-# overlappable #-}
  -- TODO: decide an interface for @@ vs sbs
  (Typeable a, All2 (Compose Substitutable Term) (Code a), Generic a) => Substitutable (Term a) where
  s @@ (Var i) = maybe (Var i) id (lookupSubst i s)
  _ @@ (Con i) = Con i
  s @@ (Rec w) = Rec $ hcmap (Proxy @(Compose Substitutable Term)) (s @@) w
  ftv (Var i)  = FreeVars $ TM.one @a (Const $ IS.singleton i)
  ftv (Con _)  = FreeVars $ TM.empty
  ftv (Rec w)  =
    let a :: [FreeVars] = hcollapse $ hcmap (Proxy @(Compose Substitutable Term)) (K . ftv) w
    in foldl (\(FreeVars t1) (FreeVars t2) -> FreeVars $ TM.unionWith (\(Const s1) (Const s2) -> Const (IS.union s1 s2)) t1 t2) (FreeVars TM.empty) a
  sbs _       _ v@(Con _) = v
  sbs visited s v@(Var i) =
    case lookupSubst @a i s of
      Just v'
        | memberVisited @a i visited -> error "Inf"
        | otherwise                  -> sbs (insertVisited @a i visited) s v'
      Nothing -> v
  sbs visited s (Rec sop) = Rec $ hcmap (Proxy @(Compose Substitutable Term)) (sbs visited s) sop

-- >>> ftv acceptable
-- FreeVars { [Char] -> [1], Foo -> [1] }

foldSubstitution :: forall m. Monoid m => (forall x. WellFormed x => Term x -> m) -> Substitution -> m
foldSubstitution f (Substitution s) = mconcat . map collapseIM $ toList s
  where
    collapseIM :: TM.WrapTypeable (Constrained WellFormed (IM.IntMap :.: Term)) -> m
    collapseIM (TM.WrapTypeable (Constrained (Comp ita))) = IM.foldr (\ta m -> f ta <> m) mempty ita

instance Substitutable Substitution where
  s1 @@ s2 = s1 `unionSubst` s2
  ftv s    = foldSubstitution ftv s
  sbs      = undefined
