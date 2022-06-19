module VerifiedTypeClasses.VerifiedMonad where

open import Haskell.Prim
open import Haskell.Prim.Monad
open import Haskell.Prim.Maybe
open import Haskell.Prim.Either
open import ProofUtils.ProofFunctions

-- VerifiedMonad record
record VerifiedMonad (m : Set → Set) {{@0 iM : Monad m}} : Set₁ where
    field
        @0 m-left-identity-law : {A B : Set} (x : A) → (g : A → (m B)) → (return {{iM}} x >>= g) ≡ (g x)
        @0 m-right-identity-law : {A : Set} → (x : m A) → (x >>= return) ≡ x
        @0 m-associative-law : {A B C : Set} → (x : m A) → (f : A → (m B)) → (g : B → (m C)) → ((x >>= f) >>= g) ≡ (x >>= (λ y → ((f y) >>= g)))

open VerifiedMonad ⦃ ... ⦄ public 

-- Example instances of Maybe and Either
instance
    iVerifiedMonadMaybe : VerifiedMonad Maybe
    iVerifiedMonadMaybe .m-left-identity-law x f = 
        begin
            return x >>= f
        =⟨⟩ -- applying return
            (Just x) >>= f
        =⟨⟩ -- applying >>=
            maybe Nothing f (Just x)
        =⟨⟩ -- applying maybe
            f x
        end
    iVerifiedMonadMaybe .m-right-identity-law Nothing =
        begin
            Nothing >>= return
        =⟨⟩ -- applying >>=
            maybe Nothing return Nothing
        =⟨⟩ -- applying maybe
            Nothing
        end
    iVerifiedMonadMaybe .m-right-identity-law (Just x) = 
        begin
            (Just x) >>= return
        =⟨⟩ -- applying >>=
            maybe Nothing return (Just x)
        =⟨⟩ -- applying maybe
            return x
        =⟨⟩ -- applying return
            Just x
        end

    iVerifiedMonadMaybe .m-associative-law Nothing f g =
        begin
            (Nothing >>= f) >>= g
        =⟨⟩ -- applying inner >>=
            (maybe Nothing f Nothing) >>= g
        =⟨⟩ -- applying maybe
            Nothing >>= g
        =⟨⟩ -- applying >>=
            (maybe Nothing g Nothing)
        =⟨⟩ -- applying maybe
            Nothing
        end
    iVerifiedMonadMaybe .m-associative-law (Just x) f g = 
        begin
            ((Just x) >>= f) >>= g
        =⟨⟩ -- applying inner >>=
            (maybe Nothing f (Just x)) >>= g
        =⟨⟩ -- applying maybe
            (f x) >>= g
        =⟨⟩ -- using lambda notation
            (λ y → (f y) >>= g) x
        =⟨⟩ -- unapplying maybe
            maybe Nothing (λ y → (f y) >>= g) (Just x)
        =⟨⟩ -- unapplying >>=
            (Just x) >>= ((λ y → f y >>= g))
        end

    iVerifiedMonadEither : {a : Set} → VerifiedMonad (Either a)
    iVerifiedMonadEither .m-left-identity-law x f = 
        begin
            return x >>= f
        =⟨⟩ -- applying return
            (Right x) >>= f
        =⟨⟩ -- applying >>=
            either (Left) f (Right x)
        =⟨⟩ -- applying either
            f x
        end

    iVerifiedMonadEither .m-right-identity-law (Left x) =
        begin
            (Left x) >>= return
        =⟨⟩ -- applying >>=
            either (Left) return (Left x)
        =⟨⟩ -- applying either
            (Left x)
        end
    iVerifiedMonadEither .m-right-identity-law (Right x) = 
        begin
            (Right x) >>= return
        =⟨⟩ -- applying >>=
            either (Left) return (Right x)
        =⟨⟩ -- applying either
            return x
        =⟨⟩ -- applying return
            Right x
        end

    iVerifiedMonadEither .m-associative-law (Left x) f g =
        begin
            ((Left x) >>= f) >>= g
        =⟨⟩ -- applying inner >>=
            (either (Left) f (Left x)) >>= g
        =⟨⟩ -- applying either
            (Left x) >>= g
        =⟨⟩ -- applying >>=
            (either (Left) g (Left x))
        =⟨⟩ -- applying either
            Left x
        end
    iVerifiedMonadEither .m-associative-law (Right x) f g = 
        begin
            ((Right x) >>= f) >>= g
        =⟨⟩ -- applying inner >>=
            (either (Left) f (Right x)) >>= g
        =⟨⟩ -- applying either
            (f x) >>= g
        =⟨⟩ -- using lambda notation
            (λ y → (f y) >>= g) x
        =⟨⟩ -- unapplying either
            either (Left) (λ y → (f y) >>= g) (Right x)
        =⟨⟩ -- unapplying >>=
            (Right x) >>= ((λ y → f y >>= g))
        end