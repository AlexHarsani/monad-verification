module Data.MonadReader.MyReader where

data MyReader r a = Reader (r -> a)

ask :: MyReader r r
ask = Reader id

asks :: (r -> a) -> MyReader r a
asks f = Reader f

local :: (r -> r) -> MyReader r a -> MyReader r a
local f (Reader g) = Reader (g . f)

runReader :: MyReader r a -> r -> a
runReader (Reader f) = f

instance Functor (MyReader r) where
    fmap f (Reader g) = Reader (f . g)

instance Applicative (MyReader r) where
    pure x = Reader (const x)
    Reader f <*> Reader g = Reader (\ x -> f x (g x))

instance Monad (MyReader r) where
    Reader f >>= g = Reader (\ y -> runReader (g (f y)) y)

