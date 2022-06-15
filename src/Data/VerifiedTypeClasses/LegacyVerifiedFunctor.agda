module Data.VerifiedTypeClasses.LegacyVerifiedFunctor where

open import Haskell.Prim
open import Haskell.Prim.Functor
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either
open import ProofUtils.ProofFunctions


record LegacyVerifiedFunctor (f : Set → Set) : Set₁ where
    field
        overlap {{ super }} : Functor f
        @0 id-law : {a : Set} (x : f a) → fmap id x ≡ x
        @0 composition-law : {A B C : Set} (g : B → C) → (h : A → B) → (x : f A) → fmap (g ∘ h) x ≡ (fmap g ∘ fmap h) x
        
open LegacyVerifiedFunctor ⦃ ... ⦄ public

instance
    iVerifiedFunctorMaybe : LegacyVerifiedFunctor Maybe
    iVerifiedFunctorMaybe .id-law Nothing = 
        begin
            fmap id Nothing
        =⟨⟩ -- applying fmap
            Nothing
        end
    iVerifiedFunctorMaybe .id-law (Just x) =
        begin
            fmap id (Just x)
        =⟨⟩ -- applying fmap
            Just (id x)
        =⟨⟩ -- applying id
            Just x
        end
    iVerifiedFunctorMaybe .composition-law f g Nothing = 
        begin
            fmap (f ∘ g) Nothing
        =⟨⟩ -- applying fmap
            Nothing
        =⟨⟩ -- unapplying fmap
            fmap f Nothing
        =⟨⟩ -- unapplying fmap
            fmap f (fmap g Nothing)
        =⟨⟩ -- unapplying ∘
            (fmap f ∘ fmap g) Nothing
        end
    iVerifiedFunctorMaybe .composition-law f g (Just x) = 
        begin
            fmap (f ∘ g) (Just x)
        =⟨⟩ -- applying fmap
            Just ((f ∘ g) x)
        =⟨⟩ -- applying ∘
            Just (f (g x))
        =⟨⟩ -- unapplying fmap
            fmap f (Just (g x))
        =⟨⟩ -- unapplying fmap
            fmap f (fmap g (Just x))
        =⟨⟩ -- unapplying ∘
            (fmap f ∘ fmap g) (Just x)
        end

    iVerifiedFunctorEither : {a : Set} → LegacyVerifiedFunctor (Either a)
    iVerifiedFunctorEither .id-law (Left x) = 
        begin
            fmap id (Left x)
        =⟨⟩ -- applying fmap
            Left x
        end
    iVerifiedFunctorEither .id-law (Right x) = 
        begin
            fmap id (Right x)
        =⟨⟩ -- applying fmap
            Right (id x)
        =⟨⟩ -- applying id
            Right x
        end
    iVerifiedFunctorEither .composition-law f g (Left x) = 
        begin
            fmap (f ∘ g) (Left x)
        =⟨⟩ -- applying fmap
            Left x
        =⟨⟩ -- unapplying fmap
            fmap f (Left x)
        =⟨⟩ -- unapplying fmap
            fmap f (fmap g (Left x))
        =⟨⟩ -- unapplying ∘
            (fmap f ∘ fmap g) (Left x)
        end
    iVerifiedFunctorEither .composition-law f g (Right x) = 
        begin
            fmap (f ∘ g) (Right x)
        =⟨⟩ -- applying fmap
            Right ((f ∘ g) x)
        =⟨⟩ -- applying ∘
            Right (f (g x))
        =⟨⟩ -- unapplying fmap
            fmap f (Right (g x))
        =⟨⟩ -- unapplying fmap
            fmap f (fmap g (Right x))
        =⟨⟩ -- unapplying ∘
            (fmap f ∘ fmap g) (Right x)
        end   