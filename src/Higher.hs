module Higher where

data IdentityF a f   = IdentityF (f a)
data MaybeF a f      = NothingF a | Just (f a)
data EitherF a b f g = LeftF (f a) | RightF (g a)
data TupleF f a      = TupleF (f (f a))
data ListF f a       = NilF a | ListF (f (ListF f a))
