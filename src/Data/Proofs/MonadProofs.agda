module Data.Proofs.MonadProofs where

open import Haskell.Prelude
open import ProofUtils.ProofFunctions

-- Maybe Monad

maybe-monad-left-identity-law : {A B : Set} (x : A) → (f : A → (Maybe B)) → (return x >>= f) ≡ (f x)
maybe-monad-left-identity-law x f = 
    begin
        return x >>= f
    =⟨⟩ -- applying return
        (Just x) >>= f
    =⟨⟩ -- applying >>=
        maybe Nothing f (Just x)
    =⟨⟩ -- applying maybe
        f x
    end

maybe-monad-right-identity-law : {A : Set} → (x : Maybe A) → (x >>= return) ≡ x
maybe-monad-right-identity-law Nothing =
    begin
        Nothing >>= return
    =⟨⟩ -- applying >>=
        maybe Nothing return Nothing
    =⟨⟩ -- applying maybe
        Nothing
    end
maybe-monad-right-identity-law (Just x) = 
    begin
        (Just x) >>= return
    =⟨⟩ -- applying >>=
        maybe Nothing return (Just x)
    =⟨⟩ -- applying maybe
        return x
    =⟨⟩ -- applying return
        Just x
    end

maybe-monad-associative-law : {A B C : Set} → (x : Maybe A) → (f : A → (Maybe B)) → (g : B → (Maybe C)) → ((x >>= f) >>= g) ≡ (x >>= (λ y → ((f y) >>= g)))
maybe-monad-associative-law Nothing f g =
    begin
        (Nothing >>= f) >>= g
    =⟨⟩ -- applying >>=
        (maybe Nothing f Nothing) >>= g
    =⟨⟩ -- applying maybe
        Nothing >>= g
    =⟨⟩ -- applying >>=
        (maybe Nothing g Nothing)
    =⟨⟩ -- applying maybe
        Nothing
    end
maybe-monad-associative-law (Just x) f g = 
    begin
        ((Just x) >>= f) >>= g
    =⟨⟩ -- applying >>=
        (maybe Nothing f (Just x)) >>= g
    =⟨⟩ -- applying maybe
        (f x) >>= g
    =⟨⟩ -- anonymizing function
        (λ y → (f y) >>= g) x
    =⟨⟩ -- unapplying maybe
        maybe Nothing (λ y → (f y) >>= g) (Just x)
    =⟨⟩ -- unapplying >>=
        (Just x) >>= ((λ y → f y >>= g))
    end

-- Either Monad

either-monad-left-identity-law : {A B C : Set} (x : A) → (f : A → (Either C B)) → (return x >>= f) ≡ (f x)
either-monad-left-identity-law x f = 
    begin
        return x >>= f
    =⟨⟩ -- applying return
        (Right x) >>= f
    =⟨⟩ -- applying >>=
        either (Left) f (Right x)
    =⟨⟩ -- applying either
        f x
    end

either-monad-right-identity-law : {A B : Set} → (x : Either B A) → (x >>= return) ≡ x
either-monad-right-identity-law (Left x) =
    begin
        (Left x) >>= return
    =⟨⟩ -- applying >>-
        either (Left) return (Left x)
    =⟨⟩ -- applying either
        (Left x)
    end
either-monad-right-identity-law (Right x) = 
    begin
        (Right x) >>= return
    =⟨⟩ -- applying >>=
        either (Left) return (Right x)
    =⟨⟩ -- applying either
        return x
    =⟨⟩ -- applying return
        Right x
    end

either-monad-associative-law : {A B C D : Set} → (x : Either D A) → (f : A → (Either D B)) → (g : B → (Either D C)) → ((x >>= f) >>= g) ≡ (x >>= (λ y → ((f y) >>= g)))
either-monad-associative-law (Left x) f g =
    begin
        ((Left x) >>= f) >>= g
    =⟨⟩ -- applying >>=
        (either (Left) f (Left x)) >>= g
    =⟨⟩ -- applying either
        (Left x) >>= g
    =⟨⟩ -- applying >>=
        (either (Left) g (Left x))
    =⟨⟩ -- applying either
        Left x
    end
either-monad-associative-law (Right x) f g = 
    begin
        ((Right x) >>= f) >>= g
    =⟨⟩ -- applying >>=
        (either (Left) f (Right x)) >>= g
    =⟨⟩ -- applying either
        (f x) >>= g
    =⟨⟩ -- anonymizing function
        (λ y → (f y) >>= g) x
    =⟨⟩ -- unapplying either
        either (Left) (λ y → (f y) >>= g) (Right x)
    =⟨⟩ -- unapplying >>=
        (Right x) >>= ((λ y → f y >>= g))
    end
