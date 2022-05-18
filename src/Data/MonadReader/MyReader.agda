module Data.MonadReader.MyReader where

open import Haskell.Prelude

data MyReader (r a : Set) : Set where
    Reader : (f : (r → a)) → MyReader r a

{-# COMPILE AGDA2HS MyReader #-}

ask : {r : Set} → MyReader r r
ask = Reader id
{-# COMPILE AGDA2HS ask #-}
  
asks : {r a : Set} (f : r → a) → MyReader r a
asks f = Reader f
{-# COMPILE AGDA2HS asks #-}

local : {r a : Set} (f : r → r) → MyReader r a → MyReader r a
local f (Reader g) = Reader (g ∘ f)
{-# COMPILE AGDA2HS local #-}

runReader : {@0 r a : Set} → MyReader r a → r → a
runReader (Reader f) = f
{-# COMPILE AGDA2HS runReader #-}

instance
    iFunctorReader : {@0 r : Set} → Functor (MyReader r)
    iFunctorReader .fmap f (Reader g) = Reader (f ∘ g)
    {-# COMPILE AGDA2HS iFunctorReader #-}

    iApplicativeReader : {@0 r : Set} → Applicative (MyReader r)
    iApplicativeReader .pure x = Reader (const x)
    iApplicativeReader ._<*>_ (Reader f) (Reader g) = Reader (λ x → f x (g x))
    {-# COMPILE AGDA2HS iApplicativeReader #-}

    iMonadReader : {@0 r : Set} → Monad (MyReader r)
    iMonadReader ._>>=_ (Reader f) g = Reader (λ y → (runReader (g (f y)) y))
    {-# COMPILE AGDA2HS iMonadReader #-}
