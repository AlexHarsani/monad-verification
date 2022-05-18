module Data.Proofs.ApplicativeProofs where


open import Haskell.Prelude
open import ProofUtils.ProofFunctions


-- Maybe Applicative

maybe-applicative-id-law : {A : Set} (x : Maybe A) → (pure id <*> x) ≡ x
maybe-applicative-id-law Nothing = 
    begin
        pure id <*> Nothing
    =⟨⟩ -- applying pure
        (Just id) <*> Nothing
    =⟨⟩ -- applying <*>
        Nothing
    end
maybe-applicative-id-law (Just x) = 
    begin
        pure id <*> (Just x)
    =⟨⟩ -- applying pure
        (Just id) <*> (Just x)
    =⟨⟩ -- applying <*>
        Just (id x)
    =⟨⟩ -- applying id
        Just x
    end

maybe-applicative-homomorphism-law : {A B : Set} → (f : A → B) → (x : A) → ((pure  f) <*> (pure {{iApplicativeMaybe}} x)) ≡ pure (f x)
maybe-applicative-homomorphism-law f x =
    begin
        (pure f) <*> (pure x)
    =⟨⟩ -- applying pure
        (Just f) <*> (Just x)
    =⟨⟩ -- applying <*>
        Just (f x)
    =⟨⟩ -- unapplying pure
        pure (f x)
    end

maybe-applicative-interchange-law : {A B : Set} (u : Maybe (A → B)) → (y : A) → (u <*> (pure {{iApplicativeMaybe}} y)) ≡ (_<*>_ {{iApplicativeMaybe}} (pure {{iApplicativeMaybe}} (_$ y)) u)
maybe-applicative-interchange-law Nothing x = 
    begin
        Nothing <*> (pure x)
    =⟨⟩ -- applying <*>
        Nothing
    =⟨⟩ -- unapplying <*>
        (pure (_$ x)) <*> Nothing
    end
maybe-applicative-interchange-law (Just f) x = 
    begin
        (Just f) <*> (pure x)
    =⟨⟩ -- applying pure
        (Just f) <*> (Just x)
    =⟨⟩ -- applying <*>
        Just (f x)
    =⟨⟩ -- unapplying $
        Just (f $ x)
    =⟨⟩ 
        Just ((_$ x) f)
    =⟨⟩ -- unapplying <*>
        (Just (_$ x)) <*> (Just f)
    =⟨⟩ -- unapplying pure
        (pure (_$ x)) <*> (Just f)
    end

maybe-applicative-composition-law : {A B C : Set} → (f : Maybe (B → C)) → (g : Maybe (A → B)) → (x : Maybe A) → ((pure {{iApplicativeMaybe}} (_∘_)) <*> f <*> g <*> x) ≡ (f <*> (g <*> x))
maybe-applicative-composition-law (Just f) (Just g) (Just x) =
    begin
        (pure (_∘_)) <*> (Just f) <*> (Just g) <*> (Just x)
    =⟨⟩ -- applying pure
        (Just (_∘_)) <*> (Just f) <*> (Just g) <*> (Just x)
    =⟨⟩ -- applying <*>
        (Just (f ∘_)) <*> (Just g) <*> (Just x)
    =⟨⟩ -- applying <*>
        (Just (f ∘ g)) <*> (Just x)
    =⟨⟩ -- applying <*>
        (Just ((f ∘ g) x))
    =⟨⟩ -- applying ∘
        (Just (f (g x)))
    =⟨⟩ -- unapplying <*>
        (Just f) <*> (Just (g x))
    =⟨⟩ -- unapplying <*>
        (Just f) <*> ((Just g) <*> (Just x))
    end
maybe-applicative-composition-law Nothing g x = 
    begin
        (pure (_∘_)) <*> Nothing <*> g <*> x
    =⟨⟩ -- applying pure
        (Just (_∘_)) <*> Nothing <*> g <*> x
    =⟨⟩ -- applying <*>
        Nothing <*> g <*> x
    end
maybe-applicative-composition-law (Just f) Nothing x = 
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
maybe-applicative-composition-law (Just f) (Just g) Nothing = 
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

-- Either Applicative

either-applicative-id-law : {A B : Set} (x : Either A B) → (pure id <*> x) ≡ x
either-applicative-id-law (Left x) = 
    begin
        pure id <*> (Left x)
    =⟨⟩ -- applying pure
        (Right id) <*> (Left x)
    =⟨⟩ -- applying <*>
        Left x
    end
either-applicative-id-law (Right x) = 
    begin
        pure id <*> (Right x)
    =⟨⟩ -- applying pure
        (Right id) <*> (Right x)
    =⟨⟩ -- applying <*>
        Right (id x)
    =⟨⟩ -- applying id
        Right x
    end

either-applicative-homomorphism-law : {A B : Set} → (f : A → B) → (x : A) → ((pure f) <*> (pure x)) ≡ pure (f x)
either-applicative-homomorphism-law {iApplicativeEither} f x =
    begin
        (pure f) <*> (pure x)
    =⟨⟩ -- applying pure
        (Right f) <*> (Right {iApplicativeEither} x)
    =⟨⟩ -- applying <*>
        Right (f x)
    =⟨⟩ -- unapplying pure
        pure (f x)
    end

either-applicative-interchange-law : {A B C : Set} (u : Either C (A → B)) → (y : A) → (u <*> (pure {{iApplicativeEither}} y)) ≡ (_<*>_ {{iApplicativeEither}} (pure {{iApplicativeEither}} (_$ y)) u)
either-applicative-interchange-law (Left z) x = 
    begin
        (Left z) <*> (pure x)
    =⟨⟩ -- applying <*>
        Left z
    =⟨⟩ -- unapplying <*>
        (Right (_$ x)) <*> (Left z)
    =⟨⟩ -- unapplying pure
        (pure (_$ x)) <*> (Left z)
    end
either-applicative-interchange-law (Right z) x =
    begin
        (Right z) <*> (pure x)
    =⟨⟩ -- applying pure
        (Right z) <*> (Right x)
    =⟨⟩ -- applying <*>
        Right (z x)
    =⟨⟩ -- unapplying $
        Right (z $ x)
    =⟨⟩
        Right ((_$ x) z)
    =⟨⟩ -- unapplying <*>
        (Right (_$ x)) <*> (Right z)
    =⟨⟩ -- unapplying pure
        (pure (_$ x)) <*> (Right z)
    end

either-applicative-composition-law : {A B C D : Set} → (f : Either D (B → C)) → (g : Either D (A → B)) → (x : Either D A) → ((pure {{iApplicativeEither}} (_∘_)) <*> f <*> g <*> x) ≡ (f <*> (g <*> x))
either-applicative-composition-law (Left f) g x = 
    begin
        (pure (_∘_)) <*> (Left f) <*> g <*> x
    =⟨⟩ -- applying pure
        (Right (_∘_)) <*> (Left f) <*> g <*> x
    =⟨⟩ -- applying <*>
        (Left f) <*> g <*> x
    end
either-applicative-composition-law (Right f) (Left g) x = 
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
either-applicative-composition-law (Right f) (Right g) (Left x) = 
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
either-applicative-composition-law (Right f) (Right g) (Right x) =
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

 