module Data.MonadReader.MyReaderT where

open import Haskell.Prelude

-- TODO: Work in progress

data MyReaderT (r a : Set) (m : Set → Set) : Set where
    ReaderT : (f : (r → (m a))) → MyReaderT r a m

