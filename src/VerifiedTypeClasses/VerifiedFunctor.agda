module VerifiedTypeClasses.VerifiedFunctor where

open import Haskell.Prim
open import Haskell.Prim.Functor
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either
open import ProofUtils.ProofFunctions

-- VerifiedFunctor record
record VerifiedFunctor (f : Set → Set) {{@0 iF : Functor f}} : Set₁ where
    field
        @0 f-id-law : {a : Set} (x : f a) → fmap id x ≡ x
        @0 f-composition-law : {A B C : Set} (g : B → C) → (h : A → B) → (x : f A) → fmap (g ∘ h) x ≡ (fmap g ∘ fmap h) x
        
open VerifiedFunctor ⦃ ... ⦄ public 

-- Example instances of Maybe and Either
instance
    iVerifiedFunctorMaybe : VerifiedFunctor Maybe
    iVerifiedFunctorMaybe .f-id-law Nothing = 
        begin
            fmap id Nothing
        =⟨⟩ -- applying fmap
            Nothing
        end
    iVerifiedFunctorMaybe .f-id-law (Just x) =
        begin
            fmap id (Just x)
        =⟨⟩ -- applying fmap
            Just (id x)
        =⟨⟩ -- applying id
            Just x
        end
    iVerifiedFunctorMaybe .f-composition-law f g Nothing = 
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
    iVerifiedFunctorMaybe .f-composition-law f g (Just x) = 
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

    iVerifiedFunctorEither : {a : Set} → VerifiedFunctor (Either a)
    iVerifiedFunctorEither .f-id-law (Left x) = 
        begin
            fmap id (Left x)
        =⟨⟩ -- applying fmap
            Left x
        end
    iVerifiedFunctorEither .f-id-law (Right x) = 
        begin
            fmap id (Right x)
        =⟨⟩ -- applying fmap
            Right (id x)
        =⟨⟩ -- applying id
            Right x
        end
    iVerifiedFunctorEither .f-composition-law f g (Left x) = 
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
    iVerifiedFunctorEither .f-composition-law f g (Right x) = 
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