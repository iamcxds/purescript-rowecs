module Storage where

import Prelude
import Data.List (List)
import Data.List as L
import Data.Map as M
import Data.Map.Internal (keys)
import Data.Maybe (Maybe(..), isJust)
import Data.Tuple (Tuple(..), fst, snd)

class Storage (c :: Type -> Type) a where
  allocate :: c a

class
  (Storage c a) <= StorageR (c :: Type -> Type) a where
  get :: c a -> Int -> Maybe a 
  indices :: c a -> List Int
  size :: c a -> Int
  member :: c a -> Int -> Boolean

class
  (Storage c a) <= StorageW (c :: Type -> Type) a where
  set :: c a -> Int -> a -> c a
  del :: c a -> Int -> c a
  merge :: c a -> c a -> c a -- left override right, merge allocate = identity

class (StorageR c a, StorageW c a) <= StorageRW (c :: Type -> Type) a

type IntMap
  = M.Map Int

instance storageIntMap :: Storage (M.Map Int) a where
  allocate = M.empty

instance storageRIntMap :: StorageR (M.Map Int) a where
  get im ind = M.lookup ind im
  indices im = keys im
  size im = M.size im
  member im ind = M.member ind im

instance storageWIntMap :: StorageW (M.Map Int) a where
  set im ind val = M.insert ind val im
  del im ind = M.delete ind im
  merge = M.union

instance storageRWIntMap :: StorageRW (M.Map Int) a

newtype Unique a
  = Unique (Maybe (Tuple Int a)) 

instance storageUnique :: Storage Unique a where
  allocate = Unique Nothing

instance storageRUnique :: StorageR Unique a where
  get (Unique mUni) ind = do
    unique <- mUni
    if fst unique == ind then Just (snd unique) else Nothing
  indices (Unique mUni) = case mUni of
    Just uni -> L.singleton $ fst uni
    _ -> L.Nil
  size (Unique mUni) = case mUni of
    Just uni -> 1
    _ -> 0
  member a ind = isJust $ get a ind

instance storageWUnique :: StorageW Unique a where
  set old ind val = Unique $ Just (Tuple ind val)
  del (Unique mUni) ind =
    Unique
      $ do
          unique <- mUni
          if fst unique == ind then Nothing else (Just unique)
  merge new old = 
    case new of
      Unique (Just sth) -> new
      _ -> old

instance storageRWUnique :: StorageRW Unique a