module Data.MonadReader.MonadTrans where

open import Haskell.Prim
open import Haskell.Prim.Monad
open import Haskell.Prim.Applicative

record MonadTrans (t : (Set → Set) → Set → Set) {{ @0 iT : ∀ {m} -> {{Monad m}} -> Monad (t m)}} : Set₁ where
    field
        liftM : {{Monad m}} -> {@0 a : Set} →  m a → t m a
        @0 first-law : {@0 a : Set} {{iM : Monad m}} → (x : a) → liftM (return {{iM}} x) ≡ return {{iT}} x 
        @0 second-law : {a b : Set} → {{ iM : Monad m }} → (x : m a) → (f : a → (m a)) → _>>=_ {{iT}} (liftM x) ((liftM ∘ f)) ≡ liftM (x >>= f)

open MonadTrans  ⦃ ... ⦄ public 

{-# COMPILE AGDA2HS MonadTrans class #-}
 