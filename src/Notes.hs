{-# LANGUAGE TypeSynonymInstances #-}

module Notes where

newtype Unit a = Unit ()

instance Functor Unit where
    fmap _ _ = Unit ()
