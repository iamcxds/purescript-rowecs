module Main where

import Prelude
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log, logShow)
import Data.IntMap (IntMap, empty)
--import Data.Record.Extra (mapRecord, class MapRecord)
--import Type.Prelude (class RowToList)
import Type.Proxy (Proxy2(Proxy2))
import Type.Prelude(RProxy(RProxy))
import ECS


-- g :: forall a . Proxy a -> IntMap a
-- g _ = empty

-- makeWorld :: forall row row' xs a . RowToList row xs => MapRecord xs row (Proxy a) (IntMap a) row' => { | row } -> { | row' }
-- makeWorld a = mapRecord g a

u = RProxy :: RProxy (a::Int, b::String, c::Number)

v :: ECS (a::IntMap Int, b::IntMap String, c::IntMap Number)
v=allocateStorage u (Proxy2 :: Proxy2 IntMap)

w = case v of x -> x


main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  log "Hello sailor!"
  logShow w.storage.b
