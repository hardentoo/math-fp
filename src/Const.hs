{-# LANGUAGE DeriveFunctor #-}

module Const where

import Control.Applicative hiding (Const)
import Data.Monoid

newtype Const c a = Const c deriving Functor

instance Monoid c => Applicative (Const c) where
    pure _ = Const mempty
    Const f <*> Const x = Const (f `mappend` x)

instance Monoid c => Monad (Const c) where
    return = pure
    Const m >>= _ = Const m
