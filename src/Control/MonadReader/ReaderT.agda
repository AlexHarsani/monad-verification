module Control.MonadReader.ReaderT where

open import Haskell.Prelude
open import Haskell.Prim.Maybe
open import Control.MonadReader.MonadTrans
open import ProofUtils.ProofFunctions
open import VerifiedTypeClasses.VerifiedFunctor
open import VerifiedTypeClasses.VerifiedApplicative
open import VerifiedTypeClasses.VerifiedMonad

{-# FOREIGN AGDA2HS
import Control.MonadReader.MonadTrans
#-}

postulate
  functional_extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

-- ReaderT record type
record ReaderT (r : Set) (m : Set -> Set) (a : Set) : Set where
    constructor MkReaderT
    field
        readerTComputation : (r → m a)

open ReaderT public
{-# COMPILE AGDA2HS ReaderT #-}

-- Retrieves the global variable.
askT : {r : Set} {@0 m : Set → Set} {{_ : Monad m}} → ReaderT r m r
askT = MkReaderT return
{-# COMPILE AGDA2HS askT #-}
  
-- Applies the function r -> a to the global variable and retrieves it.  
asksT : {r a : Set} {@0 m : Set → Set} {{_ : Monad m}} (f : r → a) → ReaderT r m a
asksT f = MkReaderT ( return ∘ f)
{-# COMPILE AGDA2HS asksT #-}

-- Runs the new ReaderT computation with modified the global variable.
-- It will not modify the existing global variable.
localT : {r a : Set} {@0 m : Set → Set} {{_ : Monad m}} (f : r → r) → ReaderT r m a → ReaderT r m a
localT f (MkReaderT g) = MkReaderT (g ∘ f)
{-# COMPILE AGDA2HS localT #-}

-- Runs the ReaderT computation and retrieves its result.
runReaderT : {@0 r a : Set} {@0 m : Set → Set} {{_ : Monad m}} → ReaderT r m a → r → m a
runReaderT (MkReaderT f) = f
{-# COMPILE AGDA2HS runReaderT #-}

instance
    -- Functor instance
    iFunctor : {@0 r : Set} → {{Monad m}} → Functor (ReaderT r m)
    iFunctor .fmap f (MkReaderT g) = MkReaderT $ ((fmap f) ∘ g)
    {-# COMPILE AGDA2HS iFunctor #-}

    -- VerifiedFunctor instance
    iVerifiedFunctor : {@0 r : Set} → {{_ : Monad m}} → {{VerifiedFunctor m}} → VerifiedFunctor ((ReaderT r m))
    iVerifiedFunctor .f-id-law (MkReaderT f) =
        begin
            fmap id (MkReaderT f)
        =⟨⟩ -- applying fmap
            (MkReaderT $ ((fmap id) ∘ f))
        =⟨⟩ -- applying ∘
            MkReaderT (λ x → ((fmap id (f x))))
        =⟨ cong (MkReaderT $_ ) (functional_extensionality (λ x → f-id-law (f x)))  ⟩ 
            (MkReaderT (λ x → f x))
        end
    iVerifiedFunctor .f-composition-law g h (MkReaderT r) = 
       begin
            fmap (g ∘ h) (MkReaderT r)
        =⟨⟩ -- applying fmap
            (MkReaderT $ ((fmap (g ∘ h)) ∘ r))
        =⟨⟩ -- applying ∘
            MkReaderT (λ x → ((fmap (g ∘ h) (r x))))
        =⟨ cong (MkReaderT $_ ) (functional_extensionality (λ x → f-composition-law g h (r x))) ⟩ 
            (fmap g ∘ fmap h) (MkReaderT r)
        end

    -- Applicative instance
    iApplicativeT : {@0 r : Set} → {{Monad m}} → Applicative (ReaderT r m)
    iApplicativeT .pure x = MkReaderT (λ _ → (pure x))
    iApplicativeT ._<*>_ (MkReaderT f) (MkReaderT g) = MkReaderT (λ x → (f x) <*> (g x))
    {-# COMPILE AGDA2HS iApplicativeT #-}

    -- VerifiedApplicative instance
    iVerifiedApplicative : {@0 r : Set} → {{_ : Monad m}} → {{VerifiedApplicative m}} → VerifiedApplicative ((ReaderT r m))
    iVerifiedApplicative .a-id-law (MkReaderT f) = 
        begin
            pure id <*> (MkReaderT f)
        =⟨⟩ -- applying pure
            (MkReaderT (λ _ → (pure id))) <*> (MkReaderT f)
        =⟨⟩ -- applying <*>
            MkReaderT ((λ x → (λ _ → (pure id)) x <*> f x))
        =⟨⟩ -- applying inner lambda
            MkReaderT ((λ x → pure id <*> f x))
        =⟨ cong (MkReaderT $_ ) (functional_extensionality (λ x → a-id-law (f x))) ⟩ 
            MkReaderT (λ x → f x)
        =⟨⟩ -- unapplying lambda notation
            MkReaderT f
        end
    iVerifiedApplicative .a-homomorphism-law f x = 
        begin
            (pure f) <*> (pure x)
        =⟨⟩ -- applying both pure
            (MkReaderT (λ _ → (pure f))) <*> (MkReaderT (λ _ → (pure x)))
        =⟨⟩ -- applying <*>
            MkReaderT ((λ y → (λ _ → (pure f)) y <*> (λ _ → (pure x)) y))
        =⟨⟩ -- applying inner lambdas
            MkReaderT ((λ y → (pure f) <*> (pure x)))
        =⟨ cong (MkReaderT $_ ) (functional_extensionality (λ y → a-homomorphism-law f x)) ⟩ 
            MkReaderT (λ y → (pure (f x)))
        =⟨⟩ -- unapplying pure
            pure (f x)
        end
    iVerifiedApplicative .a-interchange-law (MkReaderT f) x = 
        begin
            (MkReaderT f) <*> (pure x)
        =⟨⟩ -- applying pure
            (MkReaderT f) <*> (MkReaderT (λ _ → (pure x)))
        =⟨⟩ -- applying <*>
            MkReaderT (λ y → (f y) <*> ((λ _ → (pure x)) y))
        =⟨⟩ -- applying inner lambda
            MkReaderT (λ y → (f y) <*> (pure x))
        =⟨ cong (MkReaderT $_ ) (functional_extensionality (λ y → a-interchange-law (f y) x)) ⟩
            MkReaderT (λ y → pure (_$ x) <*> (f y))
        =⟨⟩ -- unapplying pure
            MkReaderT (λ y → (λ _ → pure (_$ x)) y <*> (f y))
        =⟨⟩ -- unapplying <*>
            (MkReaderT (λ _ → pure (_$ x))) <*> (MkReaderT f)
        =⟨⟩ -- unapplying pure
            pure (_$ x) <*> (MkReaderT f)
        end
    iVerifiedApplicative .a-composition-law (MkReaderT f) (MkReaderT g) (MkReaderT x) =
        begin
            (pure (_∘_)) <*> (MkReaderT f) <*> (MkReaderT g) <*> (MkReaderT x)
        =⟨⟩ -- applying pure
            MkReaderT (λ _ → (pure (_∘_))) <*> (MkReaderT f) <*> (MkReaderT g) <*> (MkReaderT x)
        =⟨⟩ -- applying first <*>
            MkReaderT (λ y → ((λ _ → (pure (_∘_))) y) <*> (f y)) <*> (MkReaderT g) <*> (MkReaderT x)
        =⟨⟩ -- applying inner lambda
            MkReaderT (λ y → (pure (_∘_)) <*> (f y)) <*> (MkReaderT g) <*> (MkReaderT x)
        =⟨⟩ -- applying second <*>
            MkReaderT (λ z → ((λ y → (pure (_∘_)) <*> (f y)) z) <*> (g z)) <*> (MkReaderT x)
        =⟨⟩ -- applying inner lambda
            MkReaderT (λ z → (pure (_∘_)) <*> (f z) <*> (g z)) <*> (MkReaderT x)
        =⟨⟩ -- applying last <*>
            MkReaderT (λ y → ((λ z → (pure (_∘_)) <*> (f z) <*> (g z)) y) <*> (x y))
        =⟨⟩ -- applying inner lambda
            MkReaderT (λ y → (pure (_∘_)) <*> (f y) <*> (g y) <*> (x y))
        =⟨ cong (MkReaderT $_ ) (functional_extensionality (λ y → a-composition-law (f y) (g y) (x y))) ⟩
            MkReaderT (λ y → ((f y) <*> ((g y) <*> (x y))))
        =⟨⟩ -- unapplying first <*>
            (MkReaderT f) <*> MkReaderT (λ y → (((g y) <*> (x y))))
        =⟨⟩ -- unapplying second <*>
            (MkReaderT f) <*> ((MkReaderT g) <*> (MkReaderT x))
        end
        
    -- Monad instance
    iMonadT : {@0 r : Set} → {{Monad m}} → Monad (ReaderT r m)
    iMonadT ._>>=_ m k = MkReaderT (λ r -> runReaderT m r >>= (λ a -> runReaderT (k a) r))
    {-# COMPILE AGDA2HS iMonadT #-}

    -- VerifiedMonad instance
    iVerifiedMonad : {@0 r : Set} → {{_ : Monad m}} → {{VerifiedMonad m}} → VerifiedMonad ((ReaderT r m))
    iVerifiedMonad {m} .m-left-identity-law x f =
        begin
            return x >>= f
        =⟨⟩ -- applying >>=
            MkReaderT (λ r -> runReaderT (return x) r >>= (λ a -> runReaderT (f a) r))
        =⟨⟩ -- applying return
            MkReaderT (λ r -> runReaderT (pure x) r >>= (λ a -> runReaderT (f a) r))
        =⟨⟩ -- applying pure
            MkReaderT (λ r -> runReaderT (MkReaderT (λ _ → (pure x))) r >>= (λ a -> runReaderT (f a) r))
        =⟨⟩ -- applying runReaderT
            MkReaderT (λ r -> (pure x) >>= (λ a -> runReaderT (f a) r))
        =⟨⟩ -- unapplying pure
            MkReaderT (λ r -> (return x) >>= (λ a -> runReaderT (f a) r))
        =⟨ cong (MkReaderT $_ ) (functional_extensionality (λ r → m-left-identity-law x (λ a -> runReaderT (f a) r))) ⟩ 
            MkReaderT (λ r -> runReaderT (f x) r)
        =⟨⟩ -- unapplying lambda notation
            MkReaderT (runReaderT (f x))
        =⟨⟩ 
            f x
        end
    iVerifiedMonad .m-right-identity-law (MkReaderT f) =
        begin
            (MkReaderT f) >>= return
        =⟨⟩ -- applying >>= and then first runReaderT
            MkReaderT (λ r -> f r >>= (λ a -> runReaderT (return a) r))
        =⟨ cong (MkReaderT $_ ) (functional_extensionality (λ r → m-right-identity-law (f r) )) ⟩
            MkReaderT (λ r -> f r)
        =⟨⟩ -- unapplying lambda notation
            MkReaderT f
        end
    iVerifiedMonad .m-associative-law (MkReaderT x) f g =
        begin
            ((MkReaderT x) >>= f) >>= g
        =⟨⟩ -- applying first >>= then first runReaderT
            ((MkReaderT (λ r -> x r >>= (λ a -> runReaderT (f a) r))) >>= g)
        =⟨⟩ -- applying second >>=
            MkReaderT (λ r -> (x r >>= (λ a -> runReaderT (f a) r)) >>= (λ a -> runReaderT (g a) r))
        =⟨ cong (MkReaderT $_ ) (functional_extensionality (λ r → m-associative-law (x r) ((λ a -> runReaderT (f a) r)) (λ a -> runReaderT (g a) r) )) ⟩
            MkReaderT (λ r -> ((x r) >>= (λ y → (((λ a -> runReaderT (f a) r)) y >>= (λ a -> runReaderT (g a) r)))))
        =⟨⟩ -- applying inner lambda
            MkReaderT (λ r -> ((x r) >>= (λ y → (runReaderT (f y) r) >>= (λ a -> runReaderT (g a) r))))
        =⟨⟩ -- unapplying inner >>= (+ a few inbetween steps)
            MkReaderT (λ r -> ((x r) >>= (λ a -> runReaderT ((f a) >>= g) r)))
        =⟨⟩ -- applying lambda notation
            MkReaderT (λ r -> x r >>= (λ a -> runReaderT ((λ y → ((f y) >>= g)) a) r))
        =⟨⟩ -- unapplying >>=
            (MkReaderT x) >>= (λ y → ((f y) >>= g))
        end

    -- MonadTrans instance
    iMonadTrans : {@0 r : Set} → MonadTrans ((ReaderT r))
    iMonadTrans .lift m = MkReaderT (λ _ -> m)
    iMonadTrans .first-law y =
        begin
            lift (return y)
        =⟨⟩ -- applying lift
            MkReaderT (λ _ -> (return y))
        =⟨⟩ -- applying return
            MkReaderT (λ _ -> (pure y))
        =⟨⟩ -- unapplying outer pure
            pure {{iApplicativeT}} y
        =⟨⟩ -- unapplying return
            return {{iMonadT}} y
        end
    iMonadTrans .second-law y f =
        begin
            (lift y) >>= (lift ∘ f)
        =⟨⟩ -- applying >>=
            MkReaderT (λ r -> runReaderT ((lift y)) r >>= (λ a -> runReaderT (lift (f a)) r))
        =⟨⟩ -- applying both runReaderT
            MkReaderT (λ r -> y >>= (λ a -> f a))
        =⟨⟩ -- removing lambda notation from f
            MkReaderT (λ r -> y >>= f)
        =⟨⟩ -- unapplying lift
            lift (y >>= f)
        end 
    {-# COMPILE AGDA2HS iMonadTrans #-}
