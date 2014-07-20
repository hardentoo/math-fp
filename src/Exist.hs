module Exists where

newtype Exists a = Exists
    { getExists :: forall r. (forall b. b -> r) -> r }
