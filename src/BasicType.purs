module BasicType where

import Storage

import Data.Foldable (foldl)
import Data.List (List, filter)
import Data.Map (Map, fromFoldable)
import Data.Maybe (Maybe(..), fromJust)
import Data.Ord (compare)
import Data.Ordering (Ordering(..))
import Data.Tuple (Tuple(..), fst, snd)
import Partial.Unsafe (unsafePartial)
import Prelude (class Show, map, show, ($), (<>))
import Prim.Row as Row
import Prim.RowList (Cons, Nil, kind RowList)
import Record (insert, get, set, delete) as Rec
import Type.Prelude (class IsSymbol, class RowToList, RLProxy(RLProxy), RProxy(RProxy), SProxy(SProxy), reflectSymbol)
import Type.Proxy (Proxy2(Proxy2))



newtype CompStorage (rowS :: # Type)
  = CompStorage (Record rowS)

-- Given a Record of Component containers, select one Component (via SProxy)
-- and return the value at a given index
read ::
  forall rowS name a c rowS'.
  StorageR c a =>
  IsSymbol name =>
  Row.Cons name (c a) rowS' rowS =>
  Record rowS -> SProxy name -> Int -> Maybe a
read csrec sPr ind = get v ind
  where
  v = (Rec.get sPr csrec) :: c a

-- Like read, but assume that value is present
unsafeRead ::
  forall rowS name a c rowS'.
  IsSymbol name =>
  Row.Cons name (c a) rowS' rowS =>
  StorageR c a =>
  Record rowS -> SProxy name -> Int -> a
unsafeRead csrec spr ind = unsafePartial $ fromJust $ get v ind
  where
  v = (Rec.get spr csrec) :: c a

-- Take a Record of Component containers and return a new one with
-- a particular Component updated/inserted at given index
write ::
  forall rowS name a c rowS'.
  StorageW c a =>
  IsSymbol name =>
  Row.Cons name (c a) rowS' rowS =>
  Record rowS -> SProxy name -> Int -> a -> Record rowS
write csrec spr ind val = stor'
  where
  intmap = (Rec.get spr csrec) :: c a

  intmap' = set intmap ind val

  stor' = Rec.set spr intmap' csrec

-- Recursive type class for traversing a RowList of Component names and types,
-- allocating a Record of Component containers of corresponding contained types
class AllocateStorage (listS :: RowList) (rowS :: # Type) (c :: Type -> Type) a | listS -> c a rowS where
  allocateStorageImpl :: RLProxy listS -> Record rowS

instance allocateStorageNil :: AllocateStorage Nil () c a where
  allocateStorageImpl _ = {}

instance allocateStorageCons ::
  ( IsSymbol name
  , Storage c a
  , Row.Cons name (c a) rowS' rowS
  , Row.Lacks name rowS'
  , AllocateStorage listS' rowS' d b
  ) =>
  AllocateStorage (Cons name (c a) listS') rowS c a where
  allocateStorageImpl _ = Rec.insert nameP allocate rest
    where
    nameP = SProxy :: SProxy name

    rest = allocateStorageImpl (RLProxy :: RLProxy listS') :: Record rowS'

allocateStorage ::
  forall listS rowS c a.
  RowToList rowS listS =>
  AllocateStorage listS rowS c a =>
  Storage c a =>
  CompStorage rowS
allocateStorage = CompStorage $ allocateStorageImpl (RLProxy :: RLProxy listS)

-- Recursive type class implementation of Show for Record of containers
class ShowStorage (listS :: RowList) (rowS :: # Type) (c :: Type -> Type) a | listS -> c a rowS where
  showStorageImpl :: RLProxy listS -> Record rowS -> String

instance showStorageNil :: ShowStorage Nil () c a where
  showStorageImpl _ _ = ""

instance showStorageCons ::
  ( IsSymbol name
  , Storage c a
  , Show (c a)
  , Row.Cons name (c a) rowS' rowS
  , Row.Lacks name rowS'
  , ShowStorage listS' rowS' d b
  ) =>
  ShowStorage (Cons name (c a) listS') rowS c a where
  showStorageImpl _ srec = show (reflectSymbol nameP) <> " : " <> show (Rec.get nameP srec) <> "\n" <> rest
    where
    nameP = SProxy :: SProxy name

    rest = showStorageImpl (RLProxy :: RLProxy listS') delrec

    delrec = (Rec.delete nameP srec) :: Record rowS'

-- Show instance for Record of Component containers
instance compStorageShow ::
  ( ShowStorage listS rowS c a
  , RowToList rowS listS
  ) =>
  Show (CompStorage rowS) where
  show (CompStorage srec) = showStorageImpl (RLProxy :: RLProxy listS) srec

-- Like AllocateStorage, but assuming that same container type is used for all
-- Component fields; still exists for largely sentimental reasons
class AllocateStorageUniform (listD :: RowList) (rowS :: # Type) (c :: Type -> Type) a | listD c -> rowS, rowS -> c, listD -> a where
  allocateStorageUniformImpl :: RLProxy listD -> Proxy2 c -> Record rowS

instance allocateStorageUniformNil :: AllocateStorageUniform Nil () c a where
  allocateStorageUniformImpl _ _ = {}

instance allocateStorageUniformCons ::
  ( IsSymbol name
  , Storage c a
  , Row.Cons name (c a) rowS' rowS
  , Row.Lacks name rowS'
  , AllocateStorageUniform listD' rowS' c b
  ) =>
  AllocateStorageUniform (Cons name a listD') rowS c a where
  allocateStorageUniformImpl _ _ = Rec.insert nameP allocate rest
    where
    nameP = SProxy :: SProxy name

    rest = allocateStorageUniformImpl (RLProxy :: RLProxy listD') (Proxy2 :: Proxy2 c) :: Record rowS'

allocateStorageUniform ::
  forall c rowD listD a rowS.
  RowToList rowD listD =>
  AllocateStorageUniform listD rowS c a =>
  Storage c a =>
  RProxy rowD ->
  Proxy2 c ->
  CompStorage rowS
allocateStorageUniform _ cprox = CompStorage $ allocateStorageUniformImpl (RLProxy :: RLProxy listD) cprox

-- Recursive TC:
-- Given a CompStorage with many fields and a RowList of a subset of those
-- fields, return a Record containing only the values of the specified fields
-- at a given index. Containers of other unread fields are not traversed at all.
class ReadStorage (rowS :: # Type) (listD :: RowList) (rowD :: # Type) (c :: Type -> Type) a | listD -> rowD, listD -> a, listD rowS -> c where
  readStorageImpl :: RLProxy listD -> Record rowS -> Int -> Record rowD

instance readStorageNil :: ReadStorage rowS Nil () c a where
  readStorageImpl _ _ _ = {}

instance readStorageCons ::
  ( IsSymbol name
  , StorageR c a
  , Row.Cons name a rowD' rowD
  , Row.Cons name (c a) rowS' rowS
  , Row.Lacks name rowD'
  , ReadStorage rowS listD' rowD' d b
  ) =>
  ReadStorage rowS (Cons name a listD') rowD c a where
  readStorageImpl _ srec ind = Rec.insert nameP val rest
    where
    nameP = SProxy :: SProxy name

    val = unsafeRead srec nameP ind :: a --unsafe here!

    rest = readStorageImpl (RLProxy :: RLProxy listD') srec ind

readStorage ::
  forall c rowD rowS listD a.
  RowToList rowD listD =>
  ReadStorage rowS listD rowD c a =>
  CompStorage rowS ->
  Int ->
  Record rowD
readStorage (CompStorage srec) ind = readStorageImpl (RLProxy :: RLProxy listD) srec ind

-- For applying a recently computed update (modifications or insertions) to an
-- existing CompStorage
class MergeStorage (listS :: RowList) (rowS :: # Type) (c :: Type -> Type) a | listS -> rowS c a where
  mergeStorageImpl :: RLProxy listS -> Record rowS -> Record rowS -> Record rowS

instance mergeStorageNil :: MergeStorage Nil () c a where
  mergeStorageImpl _ _ _ = {}

instance mergeStorageCons ::
  ( IsSymbol name
  , StorageW c a
  , Row.Cons name (c a) rowS' rowS
  , Row.Lacks name rowS'
  , MergeStorage listS' rowS' d b
  ) =>
  MergeStorage (Cons name (c a) listS') rowS c a where
  mergeStorageImpl _ upd inp = Rec.insert nameP val rest
    where
    nameP = SProxy :: SProxy name

    val = merge valUpd valInp

    valUpd = (Rec.get nameP upd)

    valInp = (Rec.get nameP inp)

    delUpd = (Rec.delete nameP upd) :: Record rowS'

    delInp = Rec.delete nameP inp

    rest = mergeStorageImpl (RLProxy :: RLProxy listS') delUpd delInp

mergeStorage ::
  forall rowS listS c a.
  RowToList rowS listS =>
  MergeStorage listS rowS c a =>
  CompStorage rowS ->
  CompStorage rowS ->
  CompStorage rowS
mergeStorage (CompStorage recUpd) (CompStorage recInp) = CompStorage $ mergeStorageImpl rlp recUpd recInp
  where
  rlp = RLProxy :: RLProxy listS

-- Take an index and a record of fields to write, update the specified slots
-- in the containers in the specified fields. Unwritten containers are not
-- traversed at all, just copied to output CompStorage/Record
class WriteStorage (rowS :: # Type) (listD :: RowList) (rowD :: # Type) (c :: Type -> Type) a | listD -> rowD, listD rowS -> c a where
  writeStorageImpl :: RLProxy listD -> Record rowS -> Int -> Record rowD -> Record rowS

instance writeStorageNil :: WriteStorage rowS Nil () c a where
  writeStorageImpl _ srec _ _ = srec

instance writeStorageCons ::
  ( IsSymbol name
  , StorageW c a
  , Row.Cons name a rowD' rowD
  , Row.Lacks name rowD'
  , Row.Cons name (c a) rowS' rowS
  , Row.Lacks name rowS'
  , WriteStorage rowS listD' rowD' d b
  ) =>
  WriteStorage rowS (Cons name a listD') rowD c a where
  writeStorageImpl _ srec ind drec = Rec.set nameP nstr rest
    where
    nameP = SProxy :: SProxy name

    str = (Rec.get nameP srec) :: c a

    wrdat = Rec.get nameP drec

    nstr = set str ind wrdat

    delrec = (Rec.delete nameP drec) :: Record rowD'

    rest = writeStorageImpl (RLProxy :: RLProxy listD') srec ind delrec

writeStorage ::
  forall c rowD rowS listD a.
  RowToList rowD listD =>
  WriteStorage rowS listD rowD c a =>
  CompStorage rowS ->
  Int ->
  Record rowD ->
  CompStorage rowS
writeStorage (CompStorage srec) ind drec = CompStorage $ writeStorageImpl (RLProxy :: RLProxy listD) srec ind drec

_newEntity ::
  forall c rowD rowS listD a.
  RowToList rowD listD =>
  WriteStorage rowS listD rowD c a =>
  Int ->
  Record rowD ->
  CompStorage rowS ->
  CompStorage rowS
_newEntity ind dRec (CompStorage srec) = CompStorage $ writeStorageImpl (RLProxy :: RLProxy listD) srec ind dRec



-- The fields of a CompStorage can have different numbers of elements, identify
-- the smallest and return its List of indices
class MinIndices (rowS :: # Type) (listD :: RowList) (rowD :: # Type) (c :: Type -> Type) a | listD -> rowD, listD -> a, listD rowS -> c where
  minIndicesImpl :: RLProxy listD -> Record rowS -> Tuple Int (List Int) -- why unit->???

instance minIndicesBase ::
  ( StorageR c a
  , IsSymbol name
  , Row.Cons name (c a) rowS' rowS
  ) =>
  MinIndices rowS (Cons name a Nil) rowD c a where
  minIndicesImpl _ srec = Tuple sz ind
    where
    sz = size str

    ind = indices str

    str = (Rec.get (SProxy :: SProxy name) srec)
else instance minIndicesRec ::
  ( StorageR c a
  , IsSymbol name
  , Row.Cons name a rowD' rowD
  , Row.Cons name (c a) rowS' rowS
  , Row.Lacks name rowD'
  , MinIndices rowS listD' rowD' d b
  ) =>
  MinIndices rowS (Cons name a listD') rowD c a where
  minIndicesImpl _ srec = t
    where
    str = (Rec.get (SProxy :: SProxy name) srec)

    rest = minIndicesImpl (RLProxy :: RLProxy listD') srec

    t = case compare (size str) (fst rest) of
      LT -> Tuple (size str) (indices str)
      GT -> rest
      EQ -> rest

minIndices ::
  forall c rowD rowS listD a.
  RowToList rowD listD =>
  MinIndices rowS listD rowD c a =>
  CompStorage rowS ->
  RProxy rowD ->
  List Int
minIndices (CompStorage srec) _ = indfun
  where
  indfun = snd $ minIndicesImpl (RLProxy :: RLProxy listD) srec

-- Use minIndices to get a least upper bound on intersection of index sets
-- across containers, then intersect it with the index sets of specified
-- Components
-- Component containers in fields not specified by rowD are not touched
class IntersectIndices (rowS :: # Type) (listD :: RowList) (rowD :: # Type) (c :: Type -> Type) a | listD -> rowD, listD -> a, listD rowS -> c where
  intersectIndicesImpl :: RLProxy listD -> Record rowS -> List Int -> List Int

instance intersectIndicesNil :: IntersectIndices rowS Nil () c a where
  intersectIndicesImpl _ _ iw = iw

instance intersectIndicesRec ::
  ( StorageR c a
  , IsSymbol name
  , Row.Cons name a rowD' rowD
  , Row.Cons name (c a) rowS' rowS
  , Row.Lacks name rowD'
  , IntersectIndices rowS listD' rowD' d b
  ) =>
  IntersectIndices rowS (Cons name a listD') rowD c a where
  intersectIndicesImpl _ srec iw = filter f rest
    where
    f x = member (Rec.get nameP srec) x

    nameP = SProxy :: SProxy name

    rest = intersectIndicesImpl (RLProxy :: RLProxy listD') srec iw

intersectIndices ::
  forall c rowD rowS listD a.
  RowToList rowD listD =>
  IntersectIndices rowS listD rowD c a =>
  MinIndices rowS listD rowD c a =>
  CompStorage rowS ->
  RProxy rowD ->
  List Int
intersectIndices cs@(CompStorage srec) rp = intersectIndicesImpl rlp srec minind
  where
  rlp = RLProxy :: RLProxy listD

  minind = minIndices cs rp

-- Given a CompStorage and a function from one subset of Components to another
-- apply the function at a given index (for one entity) and return the new
-- values of those fields in a new Record with only those fields
applyFn ::
  forall rowS rowD rowO listD c a.
  RowToList rowD listD =>
  ReadStorage rowS listD rowD c a =>
  Storage c a =>
  CompStorage rowS -> (Record rowD -> Record rowO) -> Int -> Record rowO
applyFn cs f ind = f sel
  where
  sel = readStorage cs ind :: Record rowD

applyFnScalar ::
  forall rowS rowD t listD c a.
  RowToList rowD listD =>
  ReadStorage rowS listD rowD c a =>
  Storage c a =>
  CompStorage rowS -> (Record rowD -> t) -> Int -> t
applyFnScalar cs f ind = f sel
  where
  sel = readStorage cs ind :: Record rowD

  {- fr :: Record rowD -> Record ( x :: t )
  fr g = { x: f g } -}

-- Take a CompStorage and a function from one subset of fields to another
-- subset. Find (using intersectIndices) the set of all indices for which
-- all input fields are present, map the function over that set, return
-- a new CompStorage with those fields updated. Containers that are neither
-- input nor output are simply copied to output CompStorage
mapFn ::
  forall rowS rowD rowO listD m1 a1 m2 a2 m3 a3 m4 a4 listO listS.
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
  (Record rowD -> Record rowO) -> CompStorage rowS -> CompStorage rowS
mapFn f cs  = mergeStorage (foldl fn empt indices') cs
  where
  empt = allocateStorage

  fn m x = writeStorage m x $ applyFn cs f x

  indices' = intersectIndices cs (RProxy :: RProxy rowD)

-- like mapFn but only change entities satisfy predication.
mapFnMaybe ::
  forall rowS rowD rowO listD m1 a1 m2 a2 m3 a3 m4 a4 listO listS.
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
  (Record rowD -> Maybe (Record rowO)) -> CompStorage rowS -> CompStorage rowS
mapFnMaybe mf cs = mergeStorage (foldl fn empty indices') cs
  where
  empty = allocateStorage

  fn m x =
    let
      recX = readStorage cs x
    in
      case mf recX of
        Just res -> writeStorage m x res
        _ -> m
        

  indices' = intersectIndices cs (RProxy :: RProxy rowD)

mapFnScalars ::
  forall rowS rowD listD m1 a1 m2 a2 t.
  RowToList rowD listD =>
  ReadStorage rowS listD rowD m1 a1 =>
  Storage m1 a1 =>
  Storage m2 a2 =>
  IntersectIndices rowS listD rowD m2 a2 =>
  MinIndices rowS listD rowD m2 a2 =>
  CompStorage rowS -> (Record rowD -> t) -> Map Int t
mapFnScalars cs f = fromFoldable $ map fn indices'
  where
  fn x =Tuple x (applyFnScalar cs f x)

  indices' = intersectIndices cs (RProxy :: RProxy rowD)



-- take a predicate from some Record type to Bool, evaluate it on all entities
-- that have the input attributes, remove ALL fields for entities that satisfied
-- predicate
class DropPred (rowS :: # Type) (listD :: RowList) (rowD :: # Type) (c :: Type -> Type) a | listD -> rowD, rowD -> a, listD rowS -> c where
  dropPredImpl :: RLProxy listD -> Record rowS -> List Int -> Record rowS

instance dropPredNil :: DropPred rowS Nil () c a where
  dropPredImpl _ srec _ = srec

instance dropPredRec ::
  ( StorageRW c a
  , IsSymbol name
  , Row.Cons name a rowD' rowD
  , Row.Cons name (c a) rowS' rowS
  , DropPred rowS listD' rowD' d b
  ) =>
  DropPred rowS (Cons name a listD') rowD c a where
  dropPredImpl _ srec ind = Rec.set nameP nstr rest
    where
    nameP = SProxy :: SProxy name

    str = (Rec.get nameP srec) :: c a

    nstr = foldl fn str ind

    fn :: c a -> Int -> c a
    fn = del

    rest = dropPredImpl (RLProxy :: RLProxy listD') srec ind

dropPred ::
  forall rowS rowD listD m1 a1 m2 a2.
  RowToList rowD listD =>
  IntersectIndices rowS listD rowD m1 a1 =>
  MinIndices rowS listD rowD m1 a1 =>
  ReadStorage rowS listD rowD m2 a2 =>
  StorageRW m1 a1 =>
  StorageR m2 a2 =>
  DropPred rowS listD rowD m1 a1 =>
  (Record rowD -> Boolean) -> CompStorage rowS ->  CompStorage rowS
dropPred p cs@(CompStorage srec) = CompStorage $ dropPredImpl (RLProxy :: RLProxy listD) srec flt
  where
  ind = intersectIndices cs (RProxy :: RProxy rowD)

  flt = filter (applyFnScalar cs p) ind



-- like WriteStorage but each field of the written record is wrapped in Maybe
-- value of Nothing means don't modify the corresponding field of the storage
class WriteMaybe (rowS :: # Type) (listM :: RowList) (rowM :: # Type) (c :: Type -> Type) a | listM -> rowM, rowM -> a, listM rowS -> c a where
  writeMaybeImpl :: RLProxy listM -> Record rowS -> Int -> Record rowM -> Record rowS

instance writeMaybeNil :: WriteMaybe rowS Nil () c a where
  writeMaybeImpl _ srec _ _ = srec

instance writeMaybeCons ::
  ( IsSymbol name
  , StorageW c a
  , Row.Cons name (Maybe a) rowM' rowM
  , Row.Lacks name rowM'
  , Row.Cons name (c a) rowS' rowS
  , Row.Lacks name rowS'
  , WriteMaybe rowS listM' rowM' d b
  ) =>
  WriteMaybe rowS (Cons name (Maybe a) listM') rowM c a where
  writeMaybeImpl _ srec ind mrec = Rec.set nameP nstr rest
    where
    nameP = SProxy :: SProxy name

    str = (Rec.get nameP srec) :: c a

    wrmay = Rec.get nameP mrec

    nstr = case wrmay of
      Nothing -> str
      Just d -> set str ind d

    delrec = (Rec.delete nameP mrec) :: Record rowM'

    rest = writeMaybeImpl (RLProxy :: RLProxy listM') srec ind delrec

writeMaybe ::
  forall c rowM rowS listM a.
  RowToList rowM listM =>
  WriteMaybe rowS listM rowM c a =>
  CompStorage rowS ->
  Int ->
  Record rowM ->
  CompStorage rowS
writeMaybe (CompStorage srec) ind mrec = CompStorage $ writeMaybeImpl (RLProxy :: RLProxy listM) srec ind mrec




