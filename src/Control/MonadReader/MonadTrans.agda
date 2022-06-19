module Control.MonadReader.MonadTrans where

open import Haskell.Prim
open import Haskell.Prim.Monad
open import Haskell.Prim.Applicative

-- Monad Trans record type.
record MonadTrans (t : (Set → Set) → Set → Set) {{ @0 iT : ∀ {m} -> {{Monad m}} -> Monad (t m)}} : Set₁ where
    field
        lift : {{Monad m}} -> {@0 a : Set} →  m a → t m a
        @0 first-law : {@0 a : Set} {{iM : Monad m}} → (x : a) → lift (return {{iM}} x) ≡ return {{iT}} x 
        @0 second-law : {a b : Set} → {{ iM : Monad m }} → (x : m a) → (f : a → (m a)) → _>>=_ {{iT}} (lift x) ((lift ∘ f)) ≡ lift (x >>= f)

open MonadTrans  ⦃ ... ⦄ public 

{-# COMPILE AGDA2HS MonadTrans class #-}
 