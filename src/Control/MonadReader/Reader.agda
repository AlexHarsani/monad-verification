module Control.MonadReader.Reader where

open import Haskell.Prelude
open import VerifiedTypeClasses.VerifiedFunctor
open import VerifiedTypeClasses.VerifiedApplicative
open import VerifiedTypeClasses.VerifiedMonad
open import ProofUtils.ProofFunctions

-- Reader record type
record Reader (r a : Set) : Set where
    constructor MkReader
    field
        readerComputation : (r → a)
        
open Reader public
{-# COMPILE AGDA2HS Reader #-}

-- Retrieves the global variable.
ask : {r : Set} → Reader r r
ask = MkReader id 
{-# COMPILE AGDA2HS ask #-}

-- Applies the function r -> a to the global variable and retrieves it.  
asks : {r a : Set} (f : r → a) → Reader r a
asks f = MkReader f
{-# COMPILE AGDA2HS asks #-}

-- Runs the new Reader computation with modified the global variable.
-- It will not modify the existing global variable.
local : {r a : Set} (f : r → r) → Reader r a → Reader r a
local f (MkReader g) = MkReader (g ∘ f)
{-# COMPILE AGDA2HS local #-}

-- Runs the Reader computation and retrieves its result.
runReader : {@0 r a : Set} → Reader r a → r → a
runReader (MkReader f) = f
{-# COMPILE AGDA2HS runReader #-}

instance
    -- Functor instance
    iFunctorReader : {@0 r : Set} → Functor (Reader r)
    iFunctorReader .fmap f (MkReader g) = MkReader (f ∘ g)
    {-# COMPILE AGDA2HS iFunctorReader #-}

    -- VerifiedFunctor instance
    iVerifiedFunctorReader : {r : Set} → VerifiedFunctor (Reader r)
    iVerifiedFunctorReader .f-id-law (MkReader f) =
        begin
            fmap id (MkReader f)
        =⟨⟩ -- applying fmap
            MkReader (id ∘ f)
        =⟨⟩ -- using lambda notation
            MkReader (λ x → id (f x))
        =⟨⟩ -- applying id
            MkReader (λ x → f x)
        =⟨⟩ -- unapplying lambda notation
            MkReader f
        end
    iVerifiedFunctorReader .f-composition-law g h (MkReader r) = 
        begin
            fmap (g ∘ h) (MkReader r)
        =⟨⟩ -- applying fmap
            MkReader ((g ∘ h) ∘ r)
        =⟨⟩ -- using lambda notation
            MkReader (λ x → (g ∘ h) (r x)) 
        =⟨⟩ -- applying ∘
            MkReader (λ x → g (h (r x)))
        =⟨⟩ -- unapplying fmap
            fmap g (MkReader (λ x → h (r x)))
        =⟨⟩ -- unapplying fmap
            fmap g (fmap h (MkReader (λ x → r x)))
        =⟨⟩ -- unapplying lambda notation
            fmap g (fmap h (MkReader r))
        =⟨⟩ -- unapplying ∘
            (fmap g ∘ fmap h) (MkReader r)
        end

    -- Applicative instance
    iApplicativeReader : {@0 r : Set} → Applicative (Reader r)
    iApplicativeReader .pure x = MkReader (const x)
    iApplicativeReader ._<*>_ (MkReader f) (MkReader g) = MkReader (λ x → f x (g x))
    {-# COMPILE AGDA2HS iApplicativeReader #-}

    -- VerifiedApplicative instance
    iVerifiedApplicativeReader : {r : Set} → VerifiedApplicative (Reader r)
    iVerifiedApplicativeReader .a-id-law (MkReader f) = 
        begin
            pure id <*> (MkReader f)
        =⟨⟩ -- applying pure
            (MkReader (const id)) <*> (MkReader f)
        =⟨⟩ -- applying <*>
            MkReader (λ x → (const id) x (f x))
        =⟨⟩ -- applying functions inside lambda notation
            MkReader (id f)
        =⟨⟩ -- applying id
            MkReader f
        end
    iVerifiedApplicativeReader .a-homomorphism-law f x = 
        begin
            (pure f) <*> (pure x)
        =⟨⟩ -- applying pure
            (MkReader (const f)) <*> (MkReader (const x))
        =⟨⟩ -- applying <*>
            MkReader (λ y → (const f) y ((const x) y))
        =⟨⟩ -- applying functions inside lambda notation
            MkReader (const (f x))
        =⟨⟩ -- unapplying pure
            pure (f x)
        end
    iVerifiedApplicativeReader .a-interchange-law (MkReader f) x = 
        begin
            (MkReader f) <*> (pure x)
        =⟨⟩ -- applying pure
            (MkReader f) <*> (MkReader (const x))
        =⟨⟩ -- applying <*>
            MkReader (λ y → f y ((const x) y))
        =⟨⟩ -- applying functions inside lambda notation
            MkReader (λ y → (const (_$ x)) y (f y))
        =⟨⟩ -- unapplying <*>
            (MkReader (const (_$ x))) <*> (MkReader f)
        =⟨⟩ -- unapplying pure
            (pure (_$ x)) <*> (MkReader f)
        end
    iVerifiedApplicativeReader .a-composition-law (MkReader f) (MkReader g) (MkReader x) =
        begin
            (pure (_∘_)) <*> (MkReader f) <*> (MkReader g) <*> (MkReader x)
        =⟨⟩ -- applying pure
            (MkReader (const (_∘_))) <*> (MkReader f) <*> (MkReader g) <*> (MkReader x)
        =⟨⟩ -- applying first <*>
            MkReader (λ y → (const (_∘_)) y (f y)) <*> (MkReader g) <*> (MkReader x)
        =⟨⟩ -- applying const (_∘_)
            MkReader (λ y → ((f y) ∘_)) <*> (MkReader g) <*> (MkReader x)
        =⟨⟩ -- applying second <*>
            MkReader (λ z → (λ y → ((f y) ∘_)) z (g z)) <*> (MkReader x)
        =⟨⟩ -- applying inner lambda
            MkReader (λ z → ((f z) ∘_) (g z)) <*> (MkReader x)
        =⟨⟩ -- applying ((f z) ∘_) (g z)
            MkReader (λ z → ((f z) ∘ (g z))) <*> (MkReader x)
        =⟨⟩ -- applying third <*>
            MkReader (λ y → (λ z → ((f z) ∘ (g z))) y (x y))
        =⟨⟩ -- applying inner lambda
            MkReader (λ y → ((f y) ∘ (g y)) (x y))
        =⟨⟩ -- applying ((f y) ∘ (g y))
            MkReader (λ y → (f y) ((g y) (x y)))
        =⟨⟩ -- unapplying <*>
            (MkReader f) <*> MkReader (λ y → (g y) (x y))
        =⟨⟩ -- unapplying <*>
            (MkReader f) <*>  ((MkReader g) <*> (MkReader x))
        end
    
    -- Monad instance
    iMonadReader : {@0 r : Set} → Monad (Reader r)
    iMonadReader ._>>=_ (MkReader f) g = MkReader (λ y → (runReader (g (f y)) y))
    {-# COMPILE AGDA2HS iMonadReader #-}

    -- VerifiedMonad instance
    iVerifiedMonadReader : {@0 r : Set} → VerifiedMonad (Reader r)
    iVerifiedMonadReader .m-left-identity-law x f =
        begin
            return x >>= f
        =⟨⟩ -- applying return
            ((MkReader (const x)) >>= f)
        =⟨⟩ -- applying >>=
            MkReader (λ y → (runReader (f ((const x) y)) y))
        =⟨⟩ -- applying const
            MkReader (λ y → runReader (f x) y)
        =⟨⟩ -- unapplying lambda notation
            MkReader (runReader (f x))
        =⟨⟩ 
            f x
        end
        
    iVerifiedMonadReader .m-right-identity-law (MkReader f) =
        begin
            (MkReader f) >>= return
        =⟨⟩ -- applying >>=
            MkReader (λ y → (runReader (return (f y)) y))
        =⟨⟩ -- applying return and runReader
            MkReader (λ y → f y)
        =⟨⟩ -- unapplying lambda notation
            MkReader f
        end
    iVerifiedMonadReader .m-associative-law (MkReader x) f g =
        begin
            ((MkReader x) >>= f) >>= g
        =⟨⟩ -- applying inner >>=
            MkReader (λ y → (runReader (f (x y)) y))  >>= g
        =⟨⟩ -- applying outer >>=
            MkReader (λ z → (runReader (g ((λ y → (runReader (f (x y)) y)) z)) z) )
        =⟨⟩ -- applying lambda
            MkReader (λ z → (runReader (g (runReader (f (x z)) z)) z) )
        =⟨⟩ -- unapplying >>= (+ a few inbetween steps)
            MkReader (λ z → (runReader ((f (x z)) >>= g) z))
        =⟨⟩ -- using lambda notation
            MkReader (λ z → (runReader ((λ y → ((f y) >>= g)) (x z)) z))
        =⟨⟩ -- unapplying >>=
            (MkReader x) >>= (λ y → ((f y) >>= g))
        end
