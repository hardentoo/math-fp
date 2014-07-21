{-# LANGUAGE DeriveFunctor #-}

module Query where

import Control.Applicative
import Data.Map as Map
import Data.Monoid
import Data.Set as Set
import Data.Traversable
import Prelude hiding (mapM)
import System.Posix.Files

data Lookup k v a = Lookup (Set k) (Map k v -> a)
    deriving Functor

instance Ord k => Applicative (Lookup k v) where
    pure = Lookup Set.empty . const
    Lookup a f <*> Lookup b x =
        Lookup (a <> b) (\m -> f m (x m))

type Stat a = Lookup FilePath FileStatus a

runStat :: Stat a -> IO a
runStat (Lookup ks f) = f . Map.fromList
    <$> mapM (\k -> (,) <$> pure k <*> callStat k) (Set.toList ks)

callStat :: FilePath -> IO FileStatus
callStat fp = do
    print $ "Calling stat: " ++ fp
    getFileStatus fp

getStat :: FilePath -> Stat FileStatus
getStat path = Lookup (Set.singleton path) (Map.! path)

getFileSize :: FilePath -> Stat Int
getFileSize path = fromIntegral . fileSize <$> getStat path

main :: IO ()
main = do
    putStrLn "Size of Query.hs"
    print =<< fileSize <$> callStat "Query.hs"
    putStrLn ""

    putStrLn "Size of Query.hs * 2 + Notes.v"
    total <- runStat $
        (+) <$> getFileSize "Yoneda.hs"
            <*> ((+) <$> getFileSize "Query.hs"
                     <*> getFileSize "Query.hs")
    print total
