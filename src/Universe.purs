module Universe where

import Prelude

import BasicType (class AllocateStorage, class DropPred, class IntersectIndices, class MergeStorage, class MinIndices, class ReadStorage, class WriteStorage, CompStorage, _newEntity, allocateStorage, dropPred, intersectIndices, mapFn, mapFnMaybe, mapFnScalars, mergeStorage, readStorage, writeStorage)
import Control.Monad.State (StateT, get, gets, modify_)
import Data.Foldable (foldM)
import Data.Lens (Lens', lens, over)
import Data.List (List(..), catMaybes,(:))
import Data.Map as M
import Data.Maybe (Maybe(..))
import Record (union)
import Storage (class Storage, class StorageR, class StorageRW)
import Type.Prelude (class RowToList, RProxy(RProxy))

type GameUniv (rowS :: # Type) (global :: # Type) = 
  {
   _ecs :: CompStorage rowS
  , _entityNum :: Int | global}
  


ecs ::forall rowS global. Lens' (GameUniv rowS global) (CompStorage rowS)
ecs = lens _._ecs ( _ {_ecs = _})

entityNum ::forall rowS global. Lens' (GameUniv rowS global) Int
entityNum = lens _._entityNum ( _ {_entityNum = _})

-- empty entity game universe.
emptyInit :: forall rowS global listS c a.
  RowToList rowS listS =>
  AllocateStorage listS rowS c a =>
  Storage c a =>
  Record global -> GameUniv rowS global
emptyInit recR = union {_ecs : allocateStorage :: CompStorage rowS , _entityNum : 0} recR :: GameUniv rowS global 

type GameState rowS global m a= StateT (GameUniv rowS global) m a


-- create a new entity with component.
newEntity :: forall c rowD rowS listD a global m.
  RowToList rowD listD =>
  WriteStorage rowS listD rowD c a =>
  (Monad m)=>
  Record rowD -> GameState rowS global m Unit
newEntity newRec = 
  do
  num <- gets _._entityNum
  modify_ $ over ecs $ _newEntity num newRec
  modify_ $ over entityNum $ (+) 1

-- delete entities with condition.
delEntity :: forall global m rowS rowD listD m1 a1 m2 a2.
  RowToList rowD listD =>
  IntersectIndices rowS listD rowD m1 a1 =>
  MinIndices rowS listD rowD m1 a1 =>
  ReadStorage rowS listD rowD m2 a2 =>
  StorageRW m1 a1 =>
  StorageR m2 a2 =>
  DropPred rowS listD rowD m1 a1 =>
  (Monad m)=>
  (Record rowD -> Boolean) -> GameState rowS global m Unit
delEntity filter = do
   modify_ $ over ecs $ dropPred filter

-- update all entities with corresponded components.
updateByComp' :: forall  global m rowS rowD rowO listD m1 a1 m2 a2 m3 a3 m4 a4 listO listS.
  RowToList rowD listD =>
  RowToList rowO listO =>
  RowToList rowS listS =>
  AllocateStorage listS rowS m1 a1 =>
  ReadStorage rowS listD rowD m2 a2 =>
  WriteStorage rowS listO rowO m3 a3 =>
  MergeStorage listS rowS m1 a1 =>
  Storage m1 a1 =>
  Storage m2 a2 =>
  Storage m3 a3 =>
  Storage m4 a4 =>
  IntersectIndices rowS listD rowD m4 a4 =>
  MinIndices rowS listD rowD m4 a4 =>
  (Monad m)=>
  (Record rowD -> Record rowO) -> GameState rowS global m Unit
updateByComp' updateFun = do 
  modify_ $ over ecs $ mapFn updateFun

-- update entities with corresponded components and return Just.
updateByComp :: forall  global m rowS rowD rowO listD m1 a1 m2 a2 m3 a3 m4 a4 listO listS.
  RowToList rowD listD =>
  RowToList rowO listO =>
  RowToList rowS listS =>
  AllocateStorage listS rowS m1 a1 =>
  ReadStorage rowS listD rowD m2 a2 =>
  WriteStorage rowS listO rowO m3 a3 =>
  MergeStorage listS rowS m1 a1 =>
  Storage m1 a1 =>
  Storage m2 a2 =>
  Storage m3 a3 =>
  Storage m4 a4 =>
  IntersectIndices rowS listD rowD m4 a4 =>
  MinIndices rowS listD rowD m4 a4 =>
  (Monad m)=>
  (Record rowD -> Maybe (Record rowO)) -> GameState rowS global m Unit
updateByComp mUpdateFun = do 
  modify_ $ over ecs $ mapFnMaybe mUpdateFun

-- update entities with side effects, only update those which returns Just .
updateMonad :: forall  global m rowS rowD rowO listD m1 a1 m2 a2 m3 a3 m4 a4 listO listS.
  RowToList rowD listD =>
  RowToList rowO listO =>
  RowToList rowS listS =>
  AllocateStorage listS rowS m1 a1 =>
  ReadStorage rowS listD rowD m2 a2 =>
  WriteStorage rowS listO rowO m3 a3 =>
  MergeStorage listS rowS m1 a1 =>
  Storage m1 a1 =>
  Storage m2 a2 =>
  Storage m3 a3 =>
  Storage m4 a4 =>
  IntersectIndices rowS listD rowD m4 a4 =>
  MinIndices rowS listD rowD m4 a4 =>
  (Monad m)=>
  (Record rowD -> GameState rowS global m (Maybe(Record rowO))) -> GameState rowS global m Unit
updateMonad mUpdateFun =
  let 
    getNewData indices = foldM fn empty indices
      where 
        empty = allocateStorage
        fn m x = do
          comps <- gets _._ecs
          let unUpdate = readStorage comps x
          mData <- mUpdateFun unUpdate
          case mData of 
            Just res -> pure $ writeStorage m x res
            _-> pure m
  in
  do 
    comps <- gets _._ecs
    let ind = intersectIndices comps (RProxy :: RProxy rowD)
    newData <- getNewData ind
    modify_ $ over ecs $ mergeStorage newData

--get data from all entities with correspond components.
getByComp' ::
  forall rowS rowD listD m1 a1 m2 a2 t global.
  RowToList rowD listD =>
  ReadStorage rowS listD rowD m1 a1 =>
  Storage m1 a1 =>
  Storage m2 a2 =>
  IntersectIndices rowS listD rowD m2 a2 =>
  MinIndices rowS listD rowD m2 a2 =>
  (Record rowD -> t) -> GameUniv rowS global ->  List t
getByComp' f univ = M.values $ mapFnScalars univ._ecs f


-- get data from entities with corresponded components and return Just.
getByComp ::
  forall rowS rowD listD m1 a1 m2 a2 t global.
  RowToList rowD listD =>
  ReadStorage rowS listD rowD m1 a1 =>
  Storage m1 a1 =>
  Storage m2 a2 =>
  IntersectIndices rowS listD rowD m2 a2 =>
  MinIndices rowS listD rowD m2 a2 =>
  (Record rowD -> Maybe t) -> GameUniv rowS global  ->  List t
getByComp mf univ = catMaybes (M.values $ mapFnScalars univ._ecs mf)

-- get data from entities with corresponded components and return Just and Indexes.
getWithId ::
  forall rowS rowD listD m1 a1 m2 a2 t global.
  RowToList rowD listD =>
  ReadStorage rowS listD rowD m1 a1 =>
  Storage m1 a1 =>
  Storage m2 a2 =>
  IntersectIndices rowS listD rowD m2 a2 =>
  MinIndices rowS listD rowD m2 a2 =>
  (Record rowD -> Maybe t) -> GameUniv rowS global  ->  M.Map Int t
getWithId mf univ = M.mapMaybe identity (mapFnScalars univ._ecs mf)

getMonad :: 
  forall rowS rowD listD m1 a1 m2 a2 t global m.
  RowToList rowD listD =>
  ReadStorage rowS listD rowD m1 a1 =>
  Storage m1 a1 =>
  Storage m2 a2 =>
  IntersectIndices rowS listD rowD m2 a2 =>
  MinIndices rowS listD rowD m2 a2 =>
  (Monad m)=>
  (Record rowD -> GameState rowS global m (Maybe t))  -> GameState rowS global m (List t)
getMonad mf =  do 
  univ <- get
  let 
    listEff = getByComp' mf univ
    addEff _list effA = do
      a <- effA 
      pure $ a : _list
  mlist <- foldM addEff Nil listEff
  pure $ catMaybes mlist