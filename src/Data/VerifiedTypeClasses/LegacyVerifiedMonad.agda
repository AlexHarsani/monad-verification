module Data.VerifiedTypeClasses.LegacyVerifiedMonad where

open import Haskell.Prim
open import Haskell.Prim.Monad
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either
open import ProofUtils.ProofFunctions


record LegacyVerifiedMonad (m : Set → Set) : Set₁ where
    field
        overlap {{ super }} : Monad m
        @0 left-identity-law : {A B : Set} (x : A) → (g : A → (m B)) → (return {{super}} x >>= g) ≡ (g x)
        @0 right-identity-law : {A : Set} → (x : m A) → (x >>= return) ≡ x
        @0 associative-law : {A B C : Set} → (x : m A) → (f : A → (m B)) → (g : B → (m C)) → ((x >>= f) >>= g) ≡ (x >>= (λ y → ((f y) >>= g)))

open LegacyVerifiedMonad ⦃ ... ⦄ public 

instance
    iVerifiedMonadMaybe : LegacyVerifiedMonad Maybe
    iVerifiedMonadMaybe .left-identity-law x f = 
        begin
            return x >>= f
        =⟨⟩ -- applying return
            (Just x) >>= f
        =⟨⟩ -- applying >>=
            maybe Nothing f (Just x)
        =⟨⟩ -- applying maybe
            f x
        end
    iVerifiedMonadMaybe .right-identity-law Nothing =
        begin
            Nothing >>= return
        =⟨⟩ -- applying >>=
            maybe Nothing return Nothing
        =⟨⟩ -- applying maybe
            Nothing
        end
    iVerifiedMonadMaybe .right-identity-law (Just x) = 
        begin
            (Just x) >>= return
        =⟨⟩ -- applying >>=
            maybe Nothing return (Just x)
        =⟨⟩ -- applying maybe
            return x
        =⟨⟩ -- applying return
            Just x
        end

    iVerifiedMonadMaybe .associative-law Nothing f g =
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
    iVerifiedMonadMaybe .associative-law (Just x) f g = 
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

    iVerifiedMonadEither : {a : Set} → LegacyVerifiedMonad (Either a)
    iVerifiedMonadEither .left-identity-law x f = 
        begin
            return x >>= f
        =⟨⟩ -- applying return
            (Right x) >>= f
        =⟨⟩ -- applying >>=
            either (Left) f (Right x)
        =⟨⟩ -- applying either
            f x
        end

    iVerifiedMonadEither .right-identity-law (Left x) =
        begin
            (Left x) >>= return
        =⟨⟩ -- applying >>-
            either (Left) return (Left x)
        =⟨⟩ -- applying either
            (Left x)
        end
    iVerifiedMonadEither .right-identity-law (Right x) = 
        begin
            (Right x) >>= return
        =⟨⟩ -- applying >>=
            either (Left) return (Right x)
        =⟨⟩ -- applying either
            return x
        =⟨⟩ -- applying return
            Right x
        end

    iVerifiedMonadEither .associative-law (Left x) f g =
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
    iVerifiedMonadEither .associative-law (Right x) f g = 
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