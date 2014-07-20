{-# LANGUAGE RankNTypes #-}

module Yoneda where

lower :: (forall r. (a -> r) -> f r) -> f a
lower k = k id

lift :: Functor f => f a -> (a -> r) -> f r
lift = flip fmap

data Yoneda f a = Yoneda (forall r. (a -> r) -> f r)

instance Functor (Yoneda f) where
    fmap g (Yoneda k) = Yoneda $ \h -> k (h . g)

lowerYoneda :: Yoneda f a -> f a
lowerYoneda (Yoneda k) = k id

liftYoneda :: Functor f => f a -> Yoneda f a
liftYoneda a = Yoneda $ \k -> fmap k a

data CoYoneda f a = forall s. CoYoneda (f s) (s -> a)

instance Functor (CoYoneda f) where
    fmap g (CoYoneda x k) = CoYoneda x (g . k)

lowerCoYoneda :: Functor f => CoYoneda f a -> f a
lowerCoYoneda (CoYoneda x k) = fmap k x

liftCoYoneda :: f a -> CoYoneda f a
liftCoYoneda x = CoYoneda x id
