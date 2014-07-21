{-# LANGUAGE DeriveFunctor #-}

module FreeMonad where

import Control.Applicative (Applicative(..))
import Control.Monad (liftM2)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans.State (StateT, runStateT, get, put)
import Data.Functor.Coyoneda (Coyoneda, liftCoyoneda, lowerM)

-- | FreeMonad is the free monad, or "the algebra for X encoded as an
--   algebraic data type".  It's identical to 'Control.Monad.Free', but uses
--   more direct names.
data FreeMonad m a
    = Return a
    | Join (m (FreeMonad m a))
    deriving Functor

instance Functor m => Monad (FreeMonad m) where
    return = Return

    Return m >>= f = f m
    Join m   >>= f = Join (fmap (>>= f) m)

instance Functor m => Applicative (FreeMonad m) where
    pure  = return
    (<*>) = liftM2 ($)

instance (MonadIO m, Functor m) => MonadIO (FreeMonad m) where
    liftIO = Join . fmap Return . liftIO
instance MonadIO m => MonadIO (Coyoneda m) where
    liftIO = liftCoyoneda . liftIO

-- | Record an operation in the parent monad within 'FreeMonad'; this way, we
--   only need to know it's a 'Functor'.  Coyoneda is used so that binds are
--   re-associated and we don't pay quadratic complexity costs for building up
--   the free monad description.
defer :: Functor m => m a -> FreeMonad (Coyoneda m) a
defer = Join . liftCoyoneda . fmap Return

-- | Reduce a 'FreeMonad' description by applying return and bind.  This is
--   the only time we need to know that 'm' is a 'Monad'.  This *evaluates*
--   the description of a monadic action, using that to build a real action;
--   it does not execute the action.
eval :: Monad m => FreeMonad (Coyoneda m) a -> m a
eval (Return a) = return a
eval (Join m)   = lowerM m >>= eval

main :: IO ()
main = do
    let m = go
    m `seq` print "built a FreeMonad description of the State action"
    let m' = eval m
    m' `seq` print "processed that into an actual State action"
    print =<< runStateT m' 10
  where
    go :: FreeMonad (Coyoneda (StateT Int IO)) String
    go = do
        x <- defer get
        liftIO $ print ("x: " ++ show x)

        defer $ put 20
        y <- defer get
        liftIO $ print ("y: " ++ show y)

        return "Foo"
