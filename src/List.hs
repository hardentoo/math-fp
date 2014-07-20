module Notes where

import Control.Applicative
import Control.Monad
import Test.QuickCheck

newtype List a = List { unList :: forall r. r -> (a -> r -> r) -> r }

-- newtype List a = List { unList :: forall r. Cont (r -> r) a }

instance Show a => Show (List a) where
    show (List h) =
        "[" ++ h "" (\a r -> if null r
                             then show a
                             else show a ++ ", " ++ r) ++ "]"

toList :: List a -> [a]
toList (List h) = h [] (:)

fromList :: [a] -> List a
fromList xs = List $ \r f -> foldr f r xs

instance Eq a => Eq (List a) where
    x == y = toList x == toList y

instance Functor List where
    fmap f (List h) = List $ \r k -> h r (k . f)

instance Applicative List where
    pure x = List $ \r k -> k x r
    List f <*> List x = List $ \r k -> f r $ \h s -> x s (k . h)

instance Monad List where
    return = pure
    List h >>= f = List $ \r k -> h r (\a s -> unList (f a) s k)

-- Relies on the laziness of foldr (in fromList) to work properly
head :: List a -> a
head (List h) = h (error "Empty list!") const

split :: List a -> List (a, List a)
split (List h) = h (List const) ssk
  where
    ssk v fk = List $ \r f ->
        f (v, List $ \s k -> unList fk s (\(v', x) _ -> k v' (unList x s k))) r

tail :: List a -> List a
tail = join . fmap snd . split

init :: List a -> List a
init (List h) = join $ h (List const) $ \v fk -> List $ \r f ->
    f (List $ \s k -> unList fk s $ \x _ -> k v (unList x s k)) r

instance Arbitrary a => Arbitrary (List a) where
    arbitrary = fmap fromList arbitrary

main :: IO ()
main = do
    quickCheck (\(x :: List Int) -> fmap id x == id x)
    let f = (+9); g = (`div` 3)
    quickCheck (\(x :: List Int) -> fmap f (fmap g x) == fmap (f . g) x)

    quickCheck (\(x :: List Int) -> (pure id <*> x) == x)
    quickCheck (\(x :: Int) -> (pure f <*> pure x) == (pure (f x) :: List Int))
    quickCheck (\(x :: Int) ->
                 (pure f <*> pure x) == (pure ($ x) <*> pure f :: List Int))
    quickCheck (\(x :: List Int) -> fmap f x == (pure f <*> x))

    let h = return . f
        k = return . g
    quickCheck (\(x :: Int) -> ((return x :: List Int) >>= h) == h x)
    quickCheck (\(x :: List Int) -> (x >>= return) == x)
    quickCheck (\(x :: List Int) ->
                 ((x >>= h) >>= k) == (x >>= (\y -> h y >>= k)))
