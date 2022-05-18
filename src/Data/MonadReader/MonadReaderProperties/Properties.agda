module Data.MonadReader.MonadReaderProperties.Properties where

open import Haskell.Prelude
open import ProofUtils.ProofFunctions
open import Data.MonadReader.MyReader

-- Work in progress

-- Functor Laws

functor-id-law : {R A : Set} (x : MyReader R A) → fmap id x ≡ x
functor-id-law (Reader f) = 
    begin
        fmap id (Reader f)
    =⟨⟩ -- applying fmap
        Reader (id ∘ f)
    =⟨⟩ -- anonymizing function
        Reader (λ x → id (f x))  
    =⟨⟩ -- applying id
        Reader (λ x → f x) 
    =⟨⟩ -- deanonymizing function
        Reader f       
    end
functor-composition-law : {R A B C : Set} (f : B → C) → (g : A → B) → (x : MyReader R A) → fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x
functor-composition-law f g (Reader h) =
    begin
        fmap (f ∘ g) (Reader h)
    =⟨⟩ -- applying fmap
        Reader ((f ∘ g) ∘ h)
    =⟨⟩ -- anonymizing function
        Reader (λ x → (f ∘ g) (h x))  
    =⟨⟩ -- applying ∘
        Reader (λ x → f (g (h x)))  
    =⟨⟩ -- unapplying fmap
        fmap f (Reader (λ x → g (h x)))
    =⟨⟩ -- unapplying fmap
        fmap f (fmap g (Reader (λ x → h x)))
    =⟨⟩ -- deanonymizing function
        fmap f (fmap g (Reader h))
    =⟨⟩ -- unapplying ∘
        (fmap f ∘ fmap g) (Reader h)
    end

-- Applicative laws

applicative-id-law : {R A : Set} (x : MyReader R A) → (pure id <*> x) ≡ x
applicative-id-law (Reader f) =
    begin
        pure id <*> (Reader f)
    =⟨⟩ -- applying pure
        (Reader (const id)) <*> (Reader f)
    =⟨⟩ -- applying <*>
        Reader (λ x → (const id x) (f x))
    =⟨⟩ -- applying const
        Reader (λ x → id (f x))
    =⟨⟩ -- applying id
        Reader (λ x → f x)
    =⟨⟩ -- deanonymizing function
        Reader f
    end

applicative-homomorphism-law : {A B R : Set} → (f : A → B) → (x : A) → ((pure f) <*> (pure x)) ≡ pure (f x)
applicative-homomorphism-law {iApplicativeReader} f g = 
    begin
        (pure f) <*> (pure g)
    =⟨⟩ -- applying pure
        (Reader (const f)) <*> (Reader {iApplicativeReader} (const g))
    =⟨⟩ -- applying <*>
        Reader (λ y → (const f) y ((const g) y))
    =⟨⟩ -- applying const
        Reader (λ y → f ((const g) y))
    =⟨⟩ -- applying const
        Reader (λ y → f g)
    =⟨⟩ -- unapplying const
        Reader (λ y → (const (f g)) y)
    =⟨⟩ -- deanonymizing function
        Reader (const (f g))
    =⟨⟩ -- unapplying pure
        pure (f g)
    end

