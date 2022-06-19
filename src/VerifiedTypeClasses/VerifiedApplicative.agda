module VerifiedTypeClasses.VerifiedApplicative where

open import Haskell.Prim
open import Haskell.Prim.Applicative
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either
open import ProofUtils.ProofFunctions

-- VerifiedApplicative record
record VerifiedApplicative (f : Set → Set) {{@0 iA : Applicative f}} : Set₁ where
    field
        @0 a-id-law : {a : Set} (x : f a) → (pure id <*> x) ≡ x
        @0 a-homomorphism-law : {A B : Set} → (g : A → B) → (x : A) → ((pure {{ iA }} g) <*> (pure x)) ≡ pure (g x)
        @0 a-interchange-law : {A B : Set} (u : f (A → B)) → (y : A) → (u <*> (pure y)) ≡ ((pure (_$ y)) <*> u)
        @0 a-composition-law : {A B C : Set} → (g : f (B → C)) → (h : f (A → B)) → (x : f A) → ((pure (_∘_)) <*> g <*> h <*> x) ≡ (g <*> (h <*> x))
        
open VerifiedApplicative ⦃ ... ⦄ public 

-- Example instances of Maybe and Either
instance
    iParametrizedVerifiedApplicativeMaybe : VerifiedApplicative Maybe
    iParametrizedVerifiedApplicativeMaybe .a-id-law Nothing = 
        begin
            pure id <*> Nothing
        =⟨⟩ -- applying pure
            (Just id) <*> Nothing
        =⟨⟩ -- applying <*>
            Nothing
        end
    iParametrizedVerifiedApplicativeMaybe .a-id-law (Just x) = 
        begin
            pure id <*> (Just x)
        =⟨⟩ -- applying pure
            (Just id) <*> (Just x)
        =⟨⟩ -- applying <*>
            Just (id x)
        =⟨⟩ -- applying id
            Just x
        end

    iParametrizedVerifiedApplicativeMaybe .a-homomorphism-law f x =
        begin
            (pure f) <*> (pure x)
        =⟨⟩ -- applying both pure
            (Just f) <*> (Just x)
        =⟨⟩ -- applying <*>
            Just (f x)
        =⟨⟩ -- unapplying pure
            pure (f x)
        end

    iParametrizedVerifiedApplicativeMaybe .a-interchange-law Nothing x = 
        begin
            Nothing <*> (pure x)
        =⟨⟩ -- applying <*>
            Nothing
        =⟨⟩ -- unapplying <*>
            (pure (_$ x)) <*> Nothing
        end
    iParametrizedVerifiedApplicativeMaybe .a-interchange-law (Just f) x = 
        begin
            (Just f) <*> (pure x)
        =⟨⟩ -- applying pure
            (Just f) <*> (Just x)
        =⟨⟩ -- applying <*>
            Just (f x)
        =⟨⟩ -- unapplying $
            Just (f $ x)
        =⟨⟩ -- extracting f
            Just ((_$ x) f)
        =⟨⟩ -- unapplying <*>
            (Just (_$ x)) <*> (Just f)
        =⟨⟩ -- unapplying pure
            (pure (_$ x)) <*> (Just f)
        end

    iParametrizedVerifiedApplicativeMaybe .a-composition-law Nothing g x = 
        begin
            (pure (_∘_)) <*> Nothing <*> g <*> x
        =⟨⟩ -- applying pure
            (Just (_∘_)) <*> Nothing <*> g <*> x
        =⟨⟩ -- applying <*>
            Nothing <*> g <*> x
        end
    iParametrizedVerifiedApplicativeMaybe .a-composition-law (Just f) Nothing x = 
        begin
            (pure (_∘_)) <*> (Just f) <*> Nothing <*> x
        =⟨⟩ -- applying pure
            (Just (_∘_)) <*> (Just f) <*> Nothing <*> x
        =⟨⟩ -- applying <*>
            (Just (f ∘_)) <*> Nothing <*> x
        =⟨⟩ -- applying <*>
            Nothing <*> x
        =⟨⟩ -- unapplying <*>
            (Just f) <*> (Nothing <*> x)
        end
    iParametrizedVerifiedApplicativeMaybe .a-composition-law (Just f) (Just g) Nothing = 
        begin
            (pure (_∘_)) <*> (Just f) <*> (Just g) <*> Nothing
        =⟨⟩ -- applying pure
            (Just (_∘_)) <*> (Just f) <*> (Just g) <*> Nothing
        =⟨⟩ -- applying <*>
            (Just (f ∘_)) <*> (Just g) <*> Nothing
        =⟨⟩ -- applying <*>
            (Just (f ∘ g)) <*> Nothing
        =⟨⟩ -- applying <*>
            Nothing
        =⟨⟩ -- unapplying <*> twice
            (Just f) <*> ((Just g) <*> Nothing)
        end
    iParametrizedVerifiedApplicativeMaybe .a-composition-law (Just f) (Just g) (Just a) =
        begin
            (pure (_∘_)) <*> (Just f) <*> (Just g) <*> (Just a)
        =⟨⟩ -- applying pure
            (Just (_∘_)) <*> (Just f) <*> (Just g) <*> (Just a)
        =⟨⟩ -- applying <*>
            (Just (f ∘_)) <*> (Just g) <*> (Just a)
        =⟨⟩ -- applying <*>
            (Just (f ∘ g)) <*> (Just a)
        =⟨⟩ -- applying <*>
            (Just ((f ∘ g) a))
        =⟨⟩ -- applying ∘
            (Just (f (g a)))
        =⟨⟩ -- unapplying <*>
            (Just f) <*> (Just (g a))
        =⟨⟩ -- unapplying <*>
            (Just f) <*> ((Just g) <*> (Just a))
        end

    iParametrizedVerifiedApplicativeEither : {a : Set} → VerifiedApplicative (Either a)
    iParametrizedVerifiedApplicativeEither .a-id-law (Left x) = 
        begin
            pure id <*> (Left x)
        =⟨⟩ -- applying pure
            (Right id) <*> (Left x)
        =⟨⟩ -- applying <*>
            Left x
        end
    iParametrizedVerifiedApplicativeEither .a-id-law (Right x) = 
        begin
            pure id <*> (Right x)
        =⟨⟩ -- applying pure
            (Right id) <*> (Right x)
        =⟨⟩ -- applying <*>
            Right (id x)
        =⟨⟩ -- applying id
            Right x
        end
        
    iParametrizedVerifiedApplicativeEither .a-homomorphism-law f x = 
        begin
            (pure f) <*> (pure x)
        =⟨⟩ -- applying pure
            (Right f) <*> (Right x)
        =⟨⟩ -- applying <*>
            Right (f x)
        =⟨⟩ -- unapplying pure
            pure (f x)
        end

    iParametrizedVerifiedApplicativeEither .a-interchange-law (Left x) y = 
        begin
            (Left x) <*> (pure y)
        =⟨⟩ -- applying <*>
            Left x
        =⟨⟩ -- unapplying <*>
            (Right (_$ y)) <*> (Left x)
        =⟨⟩ -- unapplying pure
            (pure (_$ y)) <*> (Left x)
        end
    iParametrizedVerifiedApplicativeEither .a-interchange-law (Right x) y = 
        begin
            (Right x) <*> (pure y)
        =⟨⟩ -- applying pure
            (Right x) <*> (Right y)
        =⟨⟩ -- applying <*>
            Right (x y)
        =⟨⟩ -- unapplying $
            Right (x $ y)
        =⟨⟩ -- extracting x
            Right ((_$ y) x)
        =⟨⟩ -- unapplying <*>
            (Right (_$ y)) <*> (Right x)
        =⟨⟩ -- unapplying pure
            (pure (_$ y)) <*> (Right x)
        end

    iParametrizedVerifiedApplicativeEither .a-composition-law (Left f) g x = 
        begin
            (pure (_∘_)) <*> (Left f) <*> g <*> x
        =⟨⟩ -- applying pure
            (Right (_∘_)) <*> (Left f) <*> g <*> x
        =⟨⟩ -- applying <*>
            (Left f) <*> g <*> x
        end
    iParametrizedVerifiedApplicativeEither .a-composition-law (Right f) (Left g) x = 
        begin
            (pure (_∘_)) <*> (Right f) <*> (Left g) <*> x
        =⟨⟩ -- applying pure
            (Right (_∘_)) <*> (Right f) <*> (Left g) <*> x
        =⟨⟩ -- applying <*>
            (Right (f ∘_)) <*> (Left g) <*> x
        =⟨⟩ -- applying <*>
            (Left g) <*> x
        =⟨⟩ -- unapplying <*>
            (Right f) <*> ((Left g) <*> x)
        end
    iParametrizedVerifiedApplicativeEither .a-composition-law (Right f) (Right g) (Left x) = 
        begin
            (pure (_∘_)) <*> (Right f) <*> (Right g) <*> (Left x)
        =⟨⟩ -- applying pure
            (Right (_∘_)) <*> (Right f) <*> (Right g) <*> (Left x)
        =⟨⟩ -- applying <*>
            (Right (f ∘_)) <*> (Right g) <*> (Left x)
        =⟨⟩ -- applying <*>
            (Right (f ∘ g)) <*> (Left x)
        =⟨⟩ -- applying <*>
            (Left x)
        =⟨⟩ -- unapplying <*> twice
            (Right f) <*> ((Right g) <*> (Left x))
        end
    iParametrizedVerifiedApplicativeEither .a-composition-law (Right f) (Right g) (Right x) =
        begin
            (pure (_∘_)) <*> (Right f) <*> (Right g) <*> (Right x)
        =⟨⟩ -- applying pure
            (Right (_∘_)) <*> (Right f) <*> (Right g) <*> (Right x)
        =⟨⟩ -- applying <*>
            (Right (f ∘_)) <*> (Right g) <*> (Right x)
        =⟨⟩ -- applying <*>
            (Right (f ∘ g)) <*> (Right x)
        =⟨⟩ -- applying <*>
            (Right ((f ∘ g) x))
        =⟨⟩ -- applying ∘
            (Right (f (g x)))
        =⟨⟩ -- unapplying <*>
            (Right f) <*> (Right (g x))
        =⟨⟩ -- unapplying <*>
            (Right f) <*> ((Right g) <*> (Right x))
        end

