module Data.MonadReader.ReaderT where

open import Haskell.Prelude
open import Haskell.Prim.Maybe
open import Data.MonadReader.MonadTrans
open import ProofUtils.ProofFunctions
open import Data.VerifiedTypeClasses.VerifiedFunctor
open import Data.VerifiedTypeClasses.VerifiedApplicative
open import Data.VerifiedTypeClasses.VerifiedMonad

{-# FOREIGN AGDA2HS
import Data.MonadReader.MonadTrans
#-}

postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

record ReaderT (r : Set) (m : Set -> Set) (a : Set) : Set where
    constructor MkReaderT
    field
        readerTComputation : (r → m a)

open ReaderT public
{-# COMPILE AGDA2HS ReaderT #-}

askT : {r : Set} {@0 m : Set → Set} {{_ : Monad m}} → ReaderT r m r
askT = MkReaderT return
{-# COMPILE AGDA2HS askT #-}
  
asksT : {r a : Set} {@0 m : Set → Set} (f : r → m a) → ReaderT r m a
asksT f = MkReaderT f
{-# COMPILE AGDA2HS asksT #-}

localT : {r a : Set} {@0 m : Set → Set} (f : r → r) → ReaderT r m a → ReaderT r m a
localT f (MkReaderT g) = MkReaderT (g ∘ f)
{-# COMPILE AGDA2HS localT #-}

runReaderT : {@0 r a : Set} {@0 m : Set → Set} {{@0 _ : Monad m}} → ReaderT r m a → r → m a
runReaderT (MkReaderT f) = f
{-# COMPILE AGDA2HS runReaderT #-}

instance
    iFunctor : {@0 r : Set} → {{Monad m}} → Functor (ReaderT r m)
    iFunctor .fmap f (MkReaderT g) = MkReaderT $ ((fmap f) ∘ g)
    {-# COMPILE AGDA2HS iFunctor #-}

    iVerifiedFunctor : {@0 r : Set} → {{_ : Monad m}} → {{VerifiedFunctor m}} → VerifiedFunctor ((ReaderT r m))
    iVerifiedFunctor .f-id-law (MkReaderT f) =
        begin
            fmap id (MkReaderT f)
        =⟨⟩ -- applying fmap
            (MkReaderT $ ((fmap id) ∘ f))
        =⟨⟩ 
            MkReaderT (λ x → ((fmap id (f x))))
        =⟨ cong (MkReaderT $_ ) (extensionality (λ x → f-id-law (f x)))  ⟩ 
            (MkReaderT (λ x → f x))
        end
    iVerifiedFunctor .f-composition-law g h (MkReaderT r) = 
       begin
            fmap (g ∘ h) (MkReaderT r)
        =⟨⟩ -- applying fmap
            (MkReaderT $ ((fmap (g ∘ h)) ∘ r))
        =⟨⟩ 
            MkReaderT (λ x → ((fmap (g ∘ h) (r x))))
        =⟨ cong (MkReaderT $_ ) (extensionality (λ x → f-composition-law g h (r x))) ⟩ 
            (fmap g ∘ fmap h) (MkReaderT r)
        end

    iApplicativeT : {@0 r : Set} → {{Monad m}} → Applicative (ReaderT r m)
    iApplicativeT .pure x = MkReaderT (λ _ → (pure x))
    iApplicativeT ._<*>_ (MkReaderT f) (MkReaderT g) = MkReaderT (λ x → (f x) <*> (g x))
    {-# COMPILE AGDA2HS iApplicativeT #-}

    iVerifiedApplicative : {@0 r : Set} → {{_ : Monad m}} → {{VerifiedApplicative m}} → VerifiedApplicative ((ReaderT r m))
    iVerifiedApplicative .a-id-law (MkReaderT f) = 
        begin
            pure id <*> (MkReaderT f)
        =⟨⟩ 
            (MkReaderT (λ _ → (pure id))) <*> (MkReaderT f)
        =⟨⟩ 
            MkReaderT ((λ x → (λ _ → (pure id)) x <*> f x))
        =⟨⟩ 
            MkReaderT ((λ x → pure id <*> f x))
        =⟨ cong (MkReaderT $_ ) (extensionality (λ x → a-id-law (f x))) ⟩ 
            MkReaderT (λ x → f x)
        =⟨⟩ 
            MkReaderT f
        end
    iVerifiedApplicative .a-homomorphism-law f x = 
        begin
            (pure f) <*> (pure x)
        =⟨⟩ 
            (MkReaderT (λ _ → (pure f))) <*> (MkReaderT (λ _ → (pure x)))
        =⟨⟩ 
            MkReaderT ((λ y → (λ _ → (pure f)) y <*> (λ _ → (pure x)) y))
        =⟨⟩ 
            MkReaderT ((λ y → (pure f) <*> (pure x)))
        =⟨ cong (MkReaderT $_ ) (extensionality (λ y → a-homomorphism-law f x)) ⟩ 
            MkReaderT (λ y → (pure (f x)))
        =⟨⟩ 
            pure (f x)
        end
    iVerifiedApplicative .a-interchange-law (MkReaderT f) x = 
        begin
            (MkReaderT f) <*> (pure x)
        =⟨⟩
            (MkReaderT f) <*> (MkReaderT (λ _ → (pure x)))
        =⟨⟩
            MkReaderT (λ y → (f y) <*> ((λ _ → (pure x)) y))
        =⟨⟩
            MkReaderT (λ y → (f y) <*> (pure x))
        =⟨ cong (MkReaderT $_ ) (extensionality (λ y → a-interchange-law (f y) x)) ⟩
            MkReaderT (λ y → pure (_$ x) <*> (f y))
        =⟨⟩
            MkReaderT (λ y → (λ _ → pure (_$ x)) y <*> (f y))
        =⟨⟩
            (MkReaderT (λ _ → pure (_$ x))) <*> (MkReaderT f)
        =⟨⟩
            pure (_$ x) <*> (MkReaderT f)
        end
    iVerifiedApplicative .a-composition-law (MkReaderT f) (MkReaderT g) (MkReaderT x) =
        begin
            (pure (_∘_)) <*> (MkReaderT f) <*> (MkReaderT g) <*> (MkReaderT x)
        =⟨⟩
            MkReaderT (λ _ → (pure (_∘_))) <*> (MkReaderT f) <*> (MkReaderT g) <*> (MkReaderT x)
        =⟨⟩
            MkReaderT (λ y → ((λ _ → (pure (_∘_))) y) <*> (f y)) <*> (MkReaderT g) <*> (MkReaderT x)
        =⟨⟩
            MkReaderT (λ y → (pure (_∘_)) <*> (f y)) <*> (MkReaderT g) <*> (MkReaderT x)
        =⟨⟩
            MkReaderT (λ z → ((λ y → (pure (_∘_)) <*> (f y)) z) <*> (g z)) <*> (MkReaderT x)
        =⟨⟩
            MkReaderT (λ z → (pure (_∘_)) <*> (f z) <*> (g z)) <*> (MkReaderT x)
        =⟨⟩
            MkReaderT (λ y → ((λ z → (pure (_∘_)) <*> (f z) <*> (g z)) y) <*> (x y))
        =⟨⟩
            MkReaderT (λ y → (pure (_∘_)) <*> (f y) <*> (g y) <*> (x y))
        =⟨ cong (MkReaderT $_ ) (extensionality (λ y → a-composition-law (f y) (g y) (x y))) ⟩
            MkReaderT (λ y → ((f y) <*> ((g y) <*> (x y))))
        =⟨⟩
            MkReaderT (λ y → ((f y) <*> ((g y) <*> (x y))))
        =⟨⟩
            (MkReaderT f) <*> MkReaderT (λ y → (((g y) <*> (x y))))
        =⟨⟩
            (MkReaderT f) <*> ((MkReaderT g) <*> (MkReaderT x))
        end
        
        
    iMonadT : {@0 r : Set} → {{Monad m}} → Monad (ReaderT r m)
    iMonadT ._>>=_ m k = MkReaderT (λ r -> runReaderT m r >>= (λ a -> runReaderT (k a) r))
    {-# COMPILE AGDA2HS iMonadT #-}

    iVerifiedMonad : {@0 r : Set} → {{_ : Monad m}} → {{VerifiedMonad m}} → VerifiedMonad ((ReaderT r m))
    iVerifiedMonad {m} .m-left-identity-law x f =
        begin
            return x >>= f
        =⟨⟩ 
            MkReaderT (λ r -> runReaderT (return x) r >>= (λ a -> runReaderT (f a) r))
        =⟨⟩ 
            MkReaderT (λ r -> runReaderT (pure x) r >>= (λ a -> runReaderT (f a) r))
        =⟨⟩ 
            MkReaderT (λ r -> runReaderT (MkReaderT (λ _ → (pure x))) r >>= (λ a -> runReaderT (f a) r))
        =⟨⟩ 
            MkReaderT (λ r -> (pure x) >>= (λ a -> runReaderT (f a) r))
        =⟨⟩ 
            MkReaderT (λ r -> (return x) >>= (λ a -> runReaderT (f a) r))
        =⟨ cong (MkReaderT $_ ) (extensionality (λ r → m-left-identity-law x (λ a -> runReaderT (f a) r))) ⟩ 
            MkReaderT (λ r -> runReaderT (f x) r)
        =⟨⟩ 
            MkReaderT (runReaderT (f x))
        =⟨⟩ 
            f x
        end
            
    iVerifiedMonad .m-right-identity-law (MkReaderT f) =
        begin
            (MkReaderT f) >>= return
        =⟨⟩ 
            MkReaderT (λ r -> f r >>= (λ a -> runReaderT (return a) r))
        =⟨ cong (MkReaderT $_ ) (extensionality (λ r → m-right-identity-law (f r) )) ⟩
            MkReaderT (λ r -> f r)
        =⟨⟩
            MkReaderT f
        end
        
    iVerifiedMonad .m-associative-law (MkReaderT x) f g =
        begin
            ((MkReaderT x) >>= f) >>= g
        =⟨⟩ -- applying first >>=
            ((MkReaderT (λ r -> x r >>= (λ a -> runReaderT (f a) r))) >>= g)
        =⟨⟩ -- applying second >>=
            MkReaderT (λ r -> (x r >>= (λ a -> runReaderT (f a) r)) >>= (λ a -> runReaderT (g a) r))
        =⟨ cong (MkReaderT $_ ) (extensionality (λ r → m-associative-law (x r) ((λ a -> runReaderT (f a) r)) (λ a -> runReaderT (g a) r) )) ⟩
            MkReaderT (λ r -> ((x r) >>= (λ y → (((λ a -> runReaderT (f a) r)) y >>= (λ a -> runReaderT (g a) r)))))
        =⟨⟩ -- 
            MkReaderT (λ r -> ((x r) >>= (λ y → (runReaderT (f y) r) >>= (λ a -> runReaderT (g a) r))))
        =⟨⟩
            MkReaderT (λ r -> ((x r) >>= (λ y → (runReaderT (f y) r) >>= (λ a -> runReaderT (g a) r))))
        =⟨⟩
            MkReaderT (λ r -> ((x r) >>= (λ a -> runReaderT ((f a) >>= g) r)))
        =⟨⟩
            MkReaderT (λ r -> x r >>= (λ a -> runReaderT ((λ y → ((f y) >>= g)) a) r))
        =⟨⟩
            (MkReaderT x) >>= (λ y → ((f y) >>= g))
        end

    iMonadTrans : {@0 r : Set} → MonadTrans ((ReaderT r))
    iMonadTrans .liftM m = MkReaderT (λ _ -> m)
    iMonadTrans .first-law y =
        begin
            liftM (return y)
        =⟨⟩ -- applying liftM
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
            (liftM y) >>= (liftM ∘ f)
        =⟨⟩ -- applying >>=
            MkReaderT (λ r -> (do a <- runReaderT ((liftM y)) r
                                  runReaderT (liftM (f a)) r))
        =⟨⟩ -- applying both runReaderT
            MkReaderT (λ r -> (do a <- y
                                  f a))
        =⟨⟩ -- desugaring do notation
            MkReaderT (λ r -> y >>= (λ a -> f a))
        =⟨⟩ -- removing lambda notation from f
            MkReaderT (λ r -> y >>= f)
        =⟨⟩ -- unapplying liftM
            liftM (y >>= f)
        end 
    {-# COMPILE AGDA2HS iMonadTrans #-}
