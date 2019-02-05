--------------------------------------------------------------------------------
-- |
-- Module      :  Generic.Unification.Substitution
-- Copyright   :  (C) 2018-19 Carlo Nucera
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Carlo Nucera <meditans@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module mainly defines `Substitution`s and related operations, and a
-- typeclass `Substitutable` to apply substitutions and get free variables.
--
--------------------------------------------------------------------------------

{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DerivingVia            #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs, KindSignatures   #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables, TypeApplications #-}
{-# LANGUAGE TypeOperators, UndecidableInstances                          #-}
{-# LANGUAGE DefaultSignatures #-}

module Generic.Unification.Substitution
  ( -- * Substitutions
    Substitution (..)
  , WellFormed
  , Constrained (..)
  , withConstrained
    -- ** Operations on substitutions
  , empty
  , insert
  , singleton
  , lookup
  , union
  , fold
  , substFreeVars
    -- * The Substitutable class
  , Substitutable ((@@), ftv)
    -- * Other type-indexed structures
    -- ** Free Variables
  , FreeVars (..)
  , memberFreeVars
    -- ** Visited Sets
  , Visited (..)
  , memberVisited
  , insertVisited
  ) where

import           Data.Functor.Const
import qualified Data.IntMap        as IM
import           Data.IntSet        (IntSet)
import qualified Data.IntSet        as IS
import           Data.List          (intercalate)
import           Data.Typeable
import qualified Data.TypeRepMap    as TM
import           Generics.SOP       hiding (fromList)
import           GHC.Base           (Type, coerce)
import           GHC.Exts           (fromList, toList)
import           Prelude            hiding (lookup, map)

import Generic.Unification.Term
import Generic.Unification.Term.Internal

--------------------------------------------------------------------------------
-- Constrained and WellFormed
--------------------------------------------------------------------------------

-- So our substitution should be a map from VarRep to Terms of that type! Maybe
-- we could use the indexed versions of TypeRep. At that point, the map would be

-- | A datatype that includes a constraint (this is useful because, as a
-- substitution contains heterogeneous terms, we have to be sure that those
-- terms have some common behaviour to be able to operate on them, and we use
-- Constrained to assure that).
data Constrained c f a = c a => Constrained (f a)

-- | The generic eliminator for `Constrained`
withConstrained :: (forall x. c x => f x -> r) -> Constrained c f a -> r
withConstrained f (Constrained fa) = f fa

-- | This is a class that expresses the constraint we need every type in our
-- substitution to have. It is an implementation detail of the library, but
-- helps in understanding which datatype we can have in our substitutions.
class    (Eq a, Eq (Term a), Show (Term a), Substitutable a) => WellFormed (a :: Type) where
instance (Eq a, Eq (Term a), Show (Term a), Substitutable a) => WellFormed a where

--------------------------------------------------------------------------------
-- Substitutions
--------------------------------------------------------------------------------

-- | Substitutions map variables (internally represented as Ints) to Terms of a
-- specific type. A key design principle of this library is that each type has
-- its set of variables, that do not overlap. So in the following substitution
-- the variable 1 of type Char tracks the term `Con c` while the variable 1 of
-- type Int tracks the term `Con 42`. There is no possibility of ambiguity, and
-- this simplifies the definition of Term.
--
-- >>> :set -XTypeApplications
-- >>> ex_substitution = insert @Char 1 (Con 'c') . insert @Int 1 (Con 42) $ empty :: Substitution
-- >>> ex_substitution
-- Substitution { Int -> [(1,Con 42)], Char -> [(1,Con 'c')] }
newtype Substitution = Substitution (TM.TypeRepMap (Constrained WellFormed (IM.IntMap :.: Term)))

instance Show Substitution where
  show (Substitution s) = wrap . intercalate ", " . fmap showInner $ toList s
    where
      showInner :: TM.WrapTypeable (Constrained WellFormed (IM.IntMap :.: Term)) -> String
      showInner (TM.WrapTypeable a@(Constrained (Comp im))) =
        show (typeRep a) ++ " -> " ++ show (toList im)
      wrap a = "Substitution { "  ++ a ++ " }"


-- | The empty substitution, which does not contain variable bindings
--
-- >>> empty
-- Substitution {  }
empty :: Substitution
empty = Substitution TM.empty

-- | Insert a variable binding into a substitution
--
-- >>> :set -XTypeApplications
-- >>> insert @Int 1 (Con 42) empty
-- Substitution { Int -> [(1,Con 42)] }
insert
  :: forall a. (WellFormed a, Typeable a)
  => Int -> Term a -> Substitution -> Substitution
insert i ta (Substitution subst) =
  case TM.member @a subst of
    True  -> Substitution $ TM.adjust @a (\(Constrained (Comp m)) -> Constrained $ Comp (IM.insert i ta m)) subst
    False -> Substitution $ TM.insert @a (Constrained . Comp $ IM.singleton i ta) subst

-- | A substitution with only one variable binding
--
-- >>> :set -XTypeApplications
-- >>> singleton @Int 1 (Con 42)
-- Substitution { Int -> [(1,Con 42)] }
singleton :: forall a. (WellFormed a, Typeable a) => Int -> Term a -> Substitution
singleton i t = insert i t empty

-- | Search for a variable in the substitution
--
-- >>> lookup @Int 1 $ singleton @Int 1 (Con 42)
-- Just (Con 42)
-- >>> lookup @String 1 $ singleton @Int 1 (Con 42)
-- Nothing
lookup :: forall a. (Typeable a) => Int -> Substitution -> Maybe (Term a)
lookup i (Substitution subst) = do
  Constrained (Comp internalMap) <- TM.lookup @a subst
  IM.lookup i internalMap

-- I also have to implement union of substitutions, with the same bias of those
-- in Data.Map I expect, which means that I prefer things that exists in the
-- first map if a collision should arise, because I want to use this definition
-- for the composition of substitutions.

-- | The union of two substitutions. It has the same bias of union in Data.Map,
-- if you think a substitution as a [(Type, Value)] map-like structure
--
-- >>> union (singleton @Int 1 (Con 42)) (singleton @Char 1 (Con 'c'))
-- Substitution { Int -> [(1,Con 42)], Char -> [(1,Con 'c')] }
union :: Substitution -> Substitution -> Substitution
union (Substitution s1) (Substitution s2) = Substitution $ TM.unionWith union' s1 s2
  where
    union' :: Constrained WellFormed (IM.IntMap :.: Term) a
           -> Constrained WellFormed (IM.IntMap :.: Term) a
           -> Constrained WellFormed (IM.IntMap :.: Term) a
    union' (Constrained (Comp m1)) (Constrained (Comp m2))
      = Constrained $ Comp (IM.union m1 m2)

--------------------------------------------------------------------------------
-- Unification
--------------------------------------------------------------------------------

-- | This datatype encodes the free (not bound) variables that we can have in a
-- term or a substitution. Basically, since our variables are overlappable, a
-- set of variables for every type.
--
-- >>> FreeVars (fromList [TM.WrapTypeable @Int $ Const (IS.fromList [1,2]), TM.WrapTypeable @Char $ Const (IS.fromList [1,3])])
-- FreeVars { Int -> [1,2], Char -> [1,3] }
--
-- Usually one would get a `FreeVars` from using the method `ftv` of the
-- Substitutable class.
--
-- >>> ftv (Var 1 :: Term Int)
-- FreeVars { Int -> [1] }

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
  show (FreeVars s) = wrap . intercalate ", " . fmap showInner $ toList s
    where
      showInner (TM.WrapTypeable a@(Const is)) =
        show (typeRep a) ++ " -> " ++ show (toList is)
      wrap a = "FreeVars { "  ++ a ++ " }"

-- | We can query if a variable is in the FreeVars at a certain type
--
-- >>> :set -XTypeApplications
-- >>> memberFreeVars @Int 1 (ftv (Var 1 :: Term Int))
-- True
-- >>> memberFreeVars @Int 1 (ftv (Var 1 :: Term Char))
-- False
memberFreeVars :: forall (a :: Type). (Typeable a) => Int -> FreeVars -> Bool
memberFreeVars i (FreeVars tm) =
  case TM.lookup @a tm of
    Just (Const is) -> IS.member i is
    Nothing -> False

-- | Visited sets: an abstraction in the Dijkstra paper that let us avoid
-- expensive occurs check in the substitution process, substituting it with
-- checking visited sets when the substitution is applied. This datatype is
-- representationally equivalent to `FreeVars`, ie. it is only a `IntSet` for
-- every type.
--
-- >>> Visited (fromList [TM.WrapTypeable @Int $ Const (IS.fromList [1,2]), TM.WrapTypeable @Char $ Const (IS.fromList [1,3])])
-- Visited { Int -> [1,2], Char -> [1,3] }
--
-- This datatype is only meant to be used in the library, the user shouldn't
-- need it.
newtype Visited = Visited (TM.TypeRepMap (Const IntSet :: Type -> Type))
  deriving (Semigroup, Monoid) via FreeVars

instance Show Visited where
  show (Visited s) = wrap . intercalate ", " . fmap showInner $ toList s
    where
      showInner (TM.WrapTypeable a@(Const is)) =
        show (typeRep a) ++ " -> " ++ show (toList is)
      wrap a = "Visited { "  ++ a ++ " }"

-- | We can query if a variable at a certain type has been visited
--
-- >>> :set -XTypeApplications
-- >>> memberVisited @Int 1 mempty
-- False
-- >>> memberVisited @Int 1 $ insertVisited @Int 1 mempty
-- True
memberVisited :: forall (a :: Type). (Typeable a) => Int -> Visited -> Bool
memberVisited = coerce (memberFreeVars @a)

-- | We can signal that a variable at a certain type has been visited
--
-- >>> :set -XTypeApplications
-- >>> insertVisited @Int 1 mempty
-- Visited { Int -> [1] }
insertVisited :: forall (a :: Type). (Typeable a) => Int -> Visited -> Visited
insertVisited i (Visited tm) =
  Visited $ TM.unionWith
              (\(Const is1) (Const is2) -> Const (IS.union is1 is2))
              (TM.one @a . Const $ IS.singleton i)
              tm

-- | We can fold a substitution in a monoidal value
--
-- >>> fold (\a -> [show a]) (insert @Char 1 (Con 'c') . insert @Int 1 (Con 42) $ empty)
-- ["Con 42","Con 'c'"]
fold :: forall m. Monoid m => (forall x. WellFormed x => Term x -> m) -> Substitution -> m
fold f (Substitution s) = mconcat . fmap collapseIM $ toList s
  where
    collapseIM :: TM.WrapTypeable (Constrained WellFormed (IM.IntMap :.: Term)) -> m
    collapseIM (TM.WrapTypeable (Constrained (Comp ita))) = IM.foldr (\ta m -> f ta <> m) mempty ita

-- | Take all variables that are free in a substitution. This amounts to taking
-- all the free variables of the internal terms
substFreeVars :: Substitution -> FreeVars
substFreeVars s = fold ftv s

--------------------------------------------------------------------------------
-- Substitutable
--------------------------------------------------------------------------------

-- | This class means that we can calculate the free variables of something and
-- apply to it a substitution. The default instance signatures appear duplicated
-- for a <https://github.com/haskell/haddock/issues/567 bug> of haddock.
class Substitutable a where
  -- | Apply a substitution to a term. This is also where we check for a cycle
  -- to occur, as we don't do the occur check in the unification algorithm to
  -- speed it up.
  (@@) :: Substitution -> Term a -> Maybe (Term a)
  default (@@) :: (Typeable a, All2 Substitutable (Code a), Generic a) => Substitution -> Term a -> Maybe (Term a)
  s @@ v = sbs mempty s v

  -- | Calculate the free variables of a term.
  ftv         :: Term a -> FreeVars
  default ftv :: (Typeable a, All2 Substitutable (Code a), Generic a)
              => Term a -> FreeVars
  ftv (Var i)  = FreeVars $ TM.one @a (Const $ IS.singleton i)
  ftv (Con _)  = FreeVars $ TM.empty
  ftv (Rec w)  =
    let a :: [FreeVars] = hcollapse $ hcmap (Proxy @Substitutable) (K . ftv) w
    in foldl (\(FreeVars t1) (FreeVars t2) -> FreeVars $ TM.unionWith (\(Const s1) (Const s2) -> Const (IS.union s1 s2)) t1 t2)
             (FreeVars TM.empty)
             a

  -- | Internal function for the free variables with starting substitution. It's
  -- morally (@@), but with an auxiliary visited set made explicit.
  sbs         :: Visited -> Substitution -> Term a -> Maybe (Term a)
  default sbs :: (Typeable a, All2 Substitutable (Code a), Generic a)
              => Visited -> Substitution -> Term a -> Maybe (Term a)
  sbs _       _ v@(Con _) = Just v
  sbs visited s v@(Var i) =
    case lookup @a i s of
      Just v'
        | memberVisited @a i visited -> Nothing
        | otherwise                  -> sbs (insertVisited @a i visited) s v'
      Nothing -> Just v
  sbs visited s (Rec sop) = Rec <$> hctraverse' (Proxy @Substitutable) (sbs visited s) sop

instance {-# overlaps #-} Substitutable Int where
  s @@ v = sbs mempty s v
  ftv (Var i)  = FreeVars $ TM.one @Int (Const $ IS.singleton i)
  ftv (Con _)  = FreeVars $ TM.empty
  ftv (Rec _)  = errorRecOnSimpleTypes
  sbs _       _ v@(Con _) = Just v
  sbs visited s v@(Var i) =
    case lookup @Int i s of
      Just v'
        | memberVisited @Int i visited -> Nothing
        | otherwise                    -> sbs (insertVisited @Int i visited) s v'
      Nothing -> Just v
  sbs _ _ (Rec _) = errorRecOnSimpleTypes

instance {-# overlaps #-} Substitutable Char where
  s @@ v = sbs mempty s v
  ftv (Var i)  = FreeVars $ TM.one @Char (Const $ IS.singleton i)
  ftv (Con _)  = FreeVars $ TM.empty
  ftv (Rec _)  = errorRecOnSimpleTypes
  sbs _       _ v@(Con _) = Just v
  sbs visited s v@(Var i) =
    case lookup @Char i s of
      Just v'
        | memberVisited @Char i visited -> Nothing
        | otherwise                     -> sbs (insertVisited @Char i visited) s v'
      Nothing -> Just v
  sbs _ _ (Rec _) = errorRecOnSimpleTypes

instance {-# overlappable #-}
  (Typeable a, All2 Substitutable (Code a), Generic a) => Substitutable a where
