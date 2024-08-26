module TTKV (TTKV (..), new, newIO, times, get, put, putIO) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as I
import Data.IntSet (IntSet)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe (fromMaybe)
import System.Clock (Clock (..), TimeSpec (..), getTime)

data TTKV k v = TTKV {_started :: {-# UNPACK #-} !Int, _mapping :: !(Map k (IntMap v))}
    deriving (Eq)

tsNanos :: IO Int
tsNanos = do
    TimeSpec s n <- getTime Monotonic
    pure $! fromIntegral s * 1_000_000_000 + fromIntegral n

new :: Int -> TTKV k v
new started = TTKV started M.empty

newIO :: IO (TTKV k v)
newIO = new <$> tsNanos

times :: TTKV k v -> IntSet
times (TTKV _ m) = foldMap I.keysSet $ M.elems m

get :: (Ord k) => Maybe Int -> k -> TTKV k v -> Maybe v
get t k (TTKV _ m) = snd <$> (maybe I.lookupMax I.lookupLE t =<< (m M.!? k))

put :: (Ord k) => Int -> k -> v -> TTKV k v -> TTKV k v
put t k v (TTKV s m) =
    let i = I.insert (t - s) v $! fromMaybe I.empty (m M.!? k)
     in TTKV s (M.insert k i m)

putIO :: (Ord k) => k -> v -> TTKV k v -> IO (TTKV k v)
putIO k v ttkv = (\t -> put t k v ttkv) <$> tsNanos
