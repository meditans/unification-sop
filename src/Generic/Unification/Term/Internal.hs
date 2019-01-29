--------------------------------------------------------------------------------
-- |
-- Module      :  Generic.Unification.Term.Internal
-- Copyright   :  (C) 2018-19 Carlo Nucera
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Carlo Nucera <meditans@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Convenience stuff that I don't want to be exported by Generic.Unification.Term
--------------------------------------------------------------------------------

module Generic.Unification.Term.Internal
  ( errorRecOnSimpleTypes
  ) where

-- | This error expresses the fact that I cannot have a Rec constructor in a
-- datatype which is not recursive. For this reason this error is safe to use
-- for those datatypes, like Int.
errorRecOnSimpleTypes :: a
errorRecOnSimpleTypes =
    error "You can't have a Rec constructor on primitive types"
