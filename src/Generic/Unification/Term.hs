--------------------------------------------------------------------------------
-- |
-- Module      :  Generic.Unification.Term
-- Copyright   :  (C) 2018-19 Carlo Nucera
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Carlo Nucera <meditans@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module defines the Term datatype, which represents a datatype with
-- logical variables in it (similar to the ones you might write in prolog).
-- Importantly, this is not done via the fixed point of a functor approach, like
-- in the unification-fd library, but using the generic structure of the term. A
-- key design decision in this module is that variables with different types do
-- not conflict with each other, so that you might write (add the example).
--
--------------------------------------------------------------------------------

{-# LANGUAGE DeriveGeneric, FlexibleContexts, FlexibleInstances,
             GADTs, KindSignatures, RankNTypes, ScopedTypeVariables,
             TypeApplications, UndecidableInstances #-}

module Generic.Unification.Term
  ( Term(..)
  , expandTerm
  ) where

import           Data.Char ( toLower )
import qualified GHC.Generics as GHC
import           Generics.SOP
import           Text.Show.Combinators

import Generic.Unification.Term.Internal (errorRecOnSimpleTypes)

-- | Term is the datatype which is inteded to be the equivalent of a prolog
-- term. Picture taking a haskell value, and drill some holes in it in which you
-- can put logical variables.
data Term a
  = Var Int                 -- ^ A logical variable
  | Con a                   -- ^ A constant, determinate value
  | Rec (SOP Term (Code a)) -- ^ The constructor, and recursive terms

expandTerm :: (Generic a) => a -> Term a
expandTerm = Rec . hmap (\(I a) -> Con a) . from

-- | This is an example we'll use throughout the package
data Foo = FooI Int | FooS String Foo
    deriving ( Show, Eq, GHC.Generic )

instance Generic Foo
instance HasDatatypeInfo Foo

-- TODO: Move the examples

-- | Some example terms (write the prolog equivalent)
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

-- | Make the case for smart constructors for terms.
fooS :: Term String -> Term Foo -> Term Foo
fooS ts tf = Rec . SOP . S . Z $ ts :* tf :* Nil

fooI :: Term Int -> Term Foo
fooI ti = Rec . SOP . Z $ ti :* Nil

-- Let's write again the examples from before:
ex3', ex4', ex5', ex5'var, ex5'var2 :: Term Foo
ex3' = fooI (Var 1)
ex4' = fooS (Con "ciao") (Con $ FooI 2)
ex5' = fooS (Con "ciao") (fooS (Var 1) (Con $ FooI 2))
ex5'var = fooS (Var 2) (fooS (Con "hey") (Con $ FooI 2))
ex5'var2 = fooS (Var 1) (fooS (Con "hey") (Con $ FooI 2))

-- What remains to be done here is not letting users directly write the ints,
-- but instead offering a monadic framework in which they can express variables.

--------------------------------------------------------------------------------
-- Show instances
--------------------------------------------------------------------------------
instance {-# OVERLAPS #-} Show (Term Int) where
    showsPrec = flip precShows
      where
        precShows (Var i) = showCon "Var" @| i
        precShows (Con i) = showCon "Con" @| i
        precShows (Rec _) = errorRecOnSimpleTypes

instance {-# OVERLAPS #-} Show (Term Char) where
    showsPrec = flip precShows
      where
        precShows (Var i) = showCon "Var" @| i
        precShows (Con c) = showCon "Con" @| c
        precShows (Rec _) = errorRecOnSimpleTypes

instance {-# OVERLAPS #-} Show (Term String) where
    showsPrec = flip precShows
      where
        precShows (Var i) = showCon "Var" @| i
        precShows (Con s) = showCon "Con" @| s
        precShows (Rec _) = errorRecOnSimpleTypes

instance {-# OVERLAPPABLE #-}( Show a
                             , Generic a
                             , HasDatatypeInfo a
                             , All2 (Compose Show Term) (Code a)
                             ) => Show (Term a) where
    showsPrec = flip precShows
      where
        precShows (Var i) = showCon "Var" @| i
        precShows (Con a) = showCon "Con" @| a
        precShows (Rec w) =
            let constructor :: PrecShowS =
                    showCon . lowerInitial $ case datatypeInfo (Proxy @a) of
                        ADT _ _ npConstrInfo -> (!! hindex w) . hcollapse $ hmap
                            (K . constructorName) npConstrInfo
                        Newtype _ _ constrInfo -> constructorName constrInfo
                terms :: [ PrecShowS ] = hcollapse $ hcmap
                    (Proxy @(Compose Show Term)) (K . flip showsPrec) w
            in foldl showApp constructor terms

-- >>> ex5'
-- fooS (Con "ciao") (fooS (Var 1) (Con (FooI 2)))
lowerInitial :: String -> String
lowerInitial [] = []
lowerInitial (c:cs) = toLower c:cs

-- We could add the feature of having optional names for variables, to print
-- something easier for the user. Also, we could indicate the type of a variable
-- along his number or name, so that we can distinguish 1@Int from 1@String, for
-- example.
--------------------------------------------------------------------------------
-- Eq instances
--------------------------------------------------------------------------------
instance {-# OVERLAPS #-}Eq (Term Int) where
    Con i == Con j = i == j
    Var i == Var j = i == j
    _ == _ = False

instance {-# OVERLAPS #-}Eq (Term Char) where
    Con c == Con d = c == d
    Var i == Var j = i == j
    _ == _ = False

instance {-# OVERLAPS #-}Eq (Term String) where
    Con s == Con t = s == t
    Var i == Var j = i == j
    _ == _ = False

instance {-# OVERLAPPABLE #-}( Eq a
                             , Generic a
                             , HasDatatypeInfo a
                             , All2 (Compose Eq Term) (Code a)
                             ) => Eq (Term a) where
    Con s == Con t = s == t
    Var i == Var j = i == j
    Rec r1 == Rec r2 = go r1 r2
      where
        go :: forall xss. (All2 (Compose Eq Term) xss)
            => SOP Term xss -> SOP Term xss -> Bool
        go (SOP (Z xs)) (SOP (Z ys)) = and . hcollapse $ hcliftA2
            (Proxy @(Compose Eq Term)) eq xs ys
        go (SOP (S xss)) (SOP (S yss)) = go (SOP xss) (SOP yss)
        go _ _ = False

        eq :: forall (x :: *). Eq (Term x) => Term x -> Term x -> K Bool x
        eq a b = K (a == b)
    _ == _ = False
