-- -*- eval: (med/hp '(pretty-show first-class-families generics-sop typerep-map show-combinators)) -*-

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | In this version, we consider (1, Int) and (1, Char) different variables. In
-- this way, we don't have to track which variable has which type. Indexes of
-- variables are not exposed to the user to not generate confusion.

module GenericPrologTermUniqueType where

import Generics.SOP
import qualified GHC.Generics as GHC
import Data.Char (toLower)
import Data.Typeable
import qualified Data.TypeRepMap as TM
import qualified Data.IntMap     as IM
import GHC.Base (Type)
import qualified Type.Reflection as TR
import Data.List (intercalate)
import Text.Show.Combinators
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Data.Functor.Const
import Control.Monad.State
import Control.Monad.Except

-- The usual generic-sop based infrastructure

data Term a where
  Var :: Int               -> Term a
  Con :: a                 -> Term a
  Rec :: SOP Term (Code a) -> Term a

-- And an example
data Foo = FooI Int | FooS String Foo deriving (Show, GHC.Generic)

instance Generic Foo
instance HasDatatypeInfo Foo

-- Some terms:
ex1, ex2, ex3, ex4 :: Term Foo
ex1 = Var 1
ex2 = Con (FooI 3)
ex3 = Rec . SOP . Z $ (Var 1) :* Nil
ex4 = Rec . SOP . S . Z $ (Con "ciao") :* (Con $ FooI 2) :* Nil

-- Now, we can write this term

acceptable :: Term Foo
acceptable = Rec . SOP . S . Z $ (Var 1) :* (Var 1) :* Nil

-- and this means that the two variables live at different types, so one is the
-- first variable of type String, and the second is the first variable of type
-- Foo.

-- Smart constructors for terms.
fooS :: Term String -> Term Foo -> Term Foo
fooS ts tf = Rec . SOP . S . Z $ ts :* tf :* Nil

fooI :: Term Int -> Term Foo
fooI ti = Rec . SOP . Z $ ti :* Nil

-- Let's write again the examples from before:
ex3', ex4', ex5' :: Term Foo
ex3' = fooI (Var 1)
ex4' = fooS (Con "ciao") (Con $ FooI 2)
ex5' = fooS (Con "ciao") (fooS (Var 1) (Con $ FooI 2))

-- What remains to be done here is not letting users directly write the ints,
-- but instead offering a monadic framework in which they can express variables.

--------------------------------------------------------------------------------
-- Show instances
--------------------------------------------------------------------------------

instance {-# overlaps #-} Show (Term Int) where
  showsPrec = flip precShows
    where
      precShows (Var i) = showCon "Var" @| i
      precShows (Con i) = showCon "Con" @| i
      precShows (Rec _) = error "I can't construct that value"

instance {-# overlaps #-} Show (Term Char) where
  showsPrec = flip precShows
    where
      precShows (Var i) = showCon "Var" @| i
      precShows (Con c) = showCon "Con" @| c
      precShows (Rec _) = error "I can't construct that value"

instance {-# overlaps #-} Show (Term String) where
  showsPrec = flip precShows
    where
      precShows (Var i) = showCon "Var" @| i
      precShows (Con s) = showCon "Con" @| s
      precShows (Rec _) = error "I can't construct that value"

instance {-# overlappable #-}
         ( Show a, Generic a, HasDatatypeInfo a
         , All2 (Compose Show Term) (Code a))
         => Show (Term a) where
  showsPrec = flip precShows
    where
      precShows (Var i) = showCon "Var" @| i
      precShows (Con a) = showCon "Con" @| a
      precShows (Rec w) =
        let 
          constructor :: PrecShowS
            = showCon . lowerInitial
            $ case datatypeInfo (Proxy @a) of
                ADT _ _ npConstrInfo
                  -> (!! hindex w) . hcollapse
                   $ hmap (K . constructorName) npConstrInfo
                Newtype _ _ constrInfo
                  -> constructorName constrInfo
          terms :: [PrecShowS]
            = hcollapse
            $ hcmap (Proxy @(Compose Show Term)) (K . flip showsPrec) w
        in foldl showApp constructor terms

-- >>> ex5'
-- fooS (Con "ciao") (fooS (Var 1) (Con (FooI 2)))

lowerInitial :: String -> String
lowerInitial [] = []
lowerInitial (c:cs) = toLower c : cs

-- We could add the feature of having optional names for variables, to print
-- something easier for the user. Also, we could indicate the type of a variable
-- along his number or name, so that we can distinguish 1@Int from 1@String, for
-- example.

--------------------------------------------------------------------------------
-- Patterns for destructuring
--------------------------------------------------------------------------------
-- We should probably supply some patterns for destructuring

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
class    (Show (Term a), Substitutable (Term a)) => WellFormed a where
instance (Show (Term a), Substitutable (Term a)) => WellFormed a where

newtype Substitution = Substitution (TM.TypeRepMap (Constrained WellFormed (IM.IntMap :.: Term)))

-- Now, convenient operation to insert something
emptySubst :: Substitution
emptySubst = Substitution TM.empty

insertSubst
  :: forall a. (Show (Term a), Substitutable (Term a), Typeable a)
  => Int -> Term a -> Substitution -> Substitution
insertSubst i ta (Substitution subst) =
  case TM.member @a subst of
    True  -> Substitution $ TM.adjust @a (\(Constrained (Comp m)) -> Constrained $ Comp (IM.insert i ta m)) subst
    False -> Substitution $ TM.insert @a (Constrained . Comp $ IM.singleton i ta) subst

ex_substitution_2 :: Substitution
ex_substitution_2 = insertSubst @Char 1 (Con 'c') $ insertSubst @Int 1 (Con 1000) emptySubst

lookupSubst :: forall a. (Typeable a) => Int -> Substitution -> Maybe (Term a)
lookupSubst i (Substitution subst) = do
  Constrained (Comp internalMap) <- TM.lookup @a subst
  IM.lookup i internalMap

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

ssss :: forall a. WellFormed a => (IM.IntMap :.: Term) a -> String
ssss a = show . unComp $ a

instance Show Substitution where
  show (Substitution s) =
    let
      ks = TM.keys s
      cs = flip map ks $ \tr ->
        case tr of
          TR.SomeTypeRep a ->
            case (TR.eqTypeRep (TR.typeRepKind a) (TR.typeRep @Type)) of
              Nothing    -> error "Kinds other then Type are not supported"
              Just HRefl ->
                case TR.withTypeable a $ lookupTM a s of
                  Nothing -> error "This case should be impossible, given that I'm searching by key"
                  -- Just tm -> show a ++ " -> " ++ withConstrained @WellFormed (show . unComp) tm
                  Just tm -> show a ++ " -> " ++ withConstrained @WellFormed (show . unComp) tm
    in "Substitution { " ++ intercalate ", " cs ++ " }"

-- >>> :set -XTypeApplications
-- >>> ex_substitution_2
-- Substitution { Int -> fromList [(1,Con 1000)], Char -> fromList [(1,Con 'c')] }

--------------------------------------------------------------------------------
-- Unification
--------------------------------------------------------------------------------
-- This is a simple account of unification following the footsteps of Parson's
-- outline. Afterwards I'll do an implementation which is more performant
-- following the ideas of fast ST-like functional references. The patterns used
-- here should be intended only to offer a simple account of unification,
-- because copying follows the unification exponential cost because of term
-- subcopying.


-- What is the simplest thing that I have to implement first? For copying, we
-- should use the approach of composing subexpressions which is outlined in the
-- account of fast unification.

occursIn :: Int -> Term a -> Bool
occursIn = undefined

-- I'll outline here the principles in the fast unification treaty: the point is
-- that if I have two substitutions theta and phi, that are seen as sets of
-- linking from one element to another, then I have to do the union of the last
-- substitution that I want to apply, and mapping over the key of the first the
-- substitution of the second. Why is this? Let's see it through an example:
-- let's say I have:
--
-- theta = [ X -> (W, Z) ]
-- phi   = [ Y -> X, X -> Y, Z -> W]

-- Let's say that I want to apply first phi. So Y becomes X, then X becomes
-- (W,Z). Then every other binding stays the same if I pick it from theta,
-- because it is the last. Summing it up:

-- At this point, the structure that contains the free variables cannot be an
-- IntSet, but has to be a TypeRepMap IntSet

newtype FreeVars = FreeVars (TM.TypeRepMap (Const IntSet :: Type -> Type))

instance Show FreeVars where
  show (FreeVars s) =
    let
      ks = TM.keys s
      cs = flip map ks $ \tr ->
        case tr of
          TR.SomeTypeRep a ->
            case (TR.eqTypeRep (TR.typeRepKind a) (TR.typeRep @Type)) of
              Nothing    -> error "Kinds other then Type are not supported"
              Just HRefl ->
                case TR.withTypeable a $ lookupTM a s of
                  Nothing -> error "This case should be impossible, given that I'm searching by key"
                  Just tm -> show a ++ " -> " ++ show tm
    in "FreeVars { " ++ intercalate ", " cs ++ " }"

class Substitutable a where
  (@@) :: Substitution -> a -> a
  ftv  :: a -> FreeVars

instance {-# overlaps #-} Substitutable (Term Int) where
  s @@ (Var i) = maybe (Var i) id (lookupSubst i s)
  _ @@ (Con i) = Con i
  _ @@ (Rec _) = error "I can't construct that value"
  ftv (Var i)  = FreeVars $ TM.one @Int (Const $ IS.singleton i)
  ftv (Con _)  = FreeVars $ TM.empty
  ftv (Rec _)  = error "I can't construct that value"

instance {-# overlaps #-} Substitutable (Term Char) where
  s @@ (Var i) = maybe (Var i) id (lookupSubst i s)
  _ @@ (Con c) = Con c
  _ @@ (Rec _) = error "I can't construct that value"
  ftv (Var i)  = FreeVars $ TM.one @Int (Const $ IS.singleton i)
  ftv (Con _)  = FreeVars $ TM.empty
  ftv (Rec _)  = error "I can't construct that value"

instance {-# overlappable #-}
  (Typeable a, All2 (Compose Substitutable Term) (Code a), All SListI (Code a)) => Substitutable (Term a) where
  s @@ (Var i) = maybe (Var i) id (lookupSubst i s)
  _ @@ (Con i) = Con i
  s @@ (Rec w) = Rec $ hcmap (Proxy @(Compose Substitutable Term)) (s @@) w
  ftv (Var i)  = FreeVars $ TM.one @a (Const $ IS.singleton i)
  ftv (Con _)  = FreeVars $ TM.empty
  ftv (Rec w)  =
    let a :: [FreeVars] = hcollapse $ hcmap (Proxy @(Compose Substitutable Term)) (K . ftv) w
    in foldl (\(FreeVars t1) (FreeVars t2) -> FreeVars $ TM.unionWith (\(Const s1) (Const s2) -> Const (IS.union s1 s2)) t1 t2) (FreeVars TM.empty) a

-- >>> ftv acceptable
-- FreeVars { [Char] -> Const (fromList [1]), Foo -> Const (fromList [1]) }

instance Substitutable Substitution where
  s1 @@ s2 = unionSubst (mapSubst (s1 @@) s2) s1
  -- ftv s = undefined

data UnificationError = UnificationError

newtype Unification a
  = Unification
  { unUnification :: ExceptT UnificationError (State Substitution) a }
  deriving (Functor, Applicative, Monad, MonadState Substitution, MonadError UnificationError)

unify :: forall a. (Eq a, Typeable a, WellFormed a, All SListI (Code a)) => Term a -> Term a -> Maybe Substitution
unify (Con t1) (Con t2)
  | t1 == t2  = Just emptySubst
  | otherwise = Nothing
unify (Var i) t
  | i `occursIn` t = Nothing
  | otherwise      = Just $ insertSubst @a i t emptySubst
unify t (Var i)
  | i `occursIn` t = Nothing
  | otherwise      = Just $ insertSubst @a i t emptySubst
unify (Rec t1) (Rec t2)
  | sameConstructor t1 t2 =
    let
      mt1   = hliftA (Comp . Just) t1
      emt1  = hexpand (Comp Nothing) mt1
      pairs = hliftA2 unsafePair emt1 t2
    in undefined
  | otherwise     = Nothing
unify _ _ = undefined

data Pair a = Pair a a

unsafePair :: forall a. (:.:) Maybe Term a -> Term a -> (Pair :.: Term) a
unsafePair (Comp (Just t1)) t2 = Comp $ Pair t1 t2
unsafePair (Comp Nothing)   _  = error "Structures should be matched"

sameConstructor :: SOP a b -> SOP a b -> Bool
sameConstructor a b = hindex a == hindex b