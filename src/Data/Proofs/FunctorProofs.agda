module Data.Proofs.FunctorProofs where


open import Haskell.Prelude
open import ProofUtils.ProofFunctions
open import Data.Tree


-- Maybe Functor

maybe-functor-id-law : {A : Set} (x : Maybe A) → fmap id x ≡ x
maybe-functor-id-law Nothing = 
    begin
        fmap id Nothing
    =⟨⟩ -- applying fmap
        Nothing
    end
maybe-functor-id-law (Just x) =
    begin
        fmap id (Just x)
    =⟨⟩ -- applying fmap
        Just (id x)
    =⟨⟩ -- applying id
        Just x
    end

maybe-functor-composition-law : {A B C : Set} (f : B → C) → (g : A → B) → (x : Maybe A) → fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x
maybe-functor-composition-law f g Nothing = 
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
maybe-functor-composition-law f g (Just x) = 
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


-- Either Functor

either-functor-id-law : {A B : Set} (x : Either A B) → fmap id x ≡ x
either-functor-id-law (Left x) = 
    begin
        fmap id (Left x)
    =⟨⟩ -- applying fmap
        Left x
    end
either-functor-id-law (Right x) = 
    begin
        fmap id (Right x)
    =⟨⟩ -- applying fmap
        Right (id x)
    =⟨⟩ -- applying id
        Right x
    end

either-functor-composition-law : {A B C D : Set} (f : B → C) → (g : A → B) → (x : Either D A) → fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x
either-functor-composition-law f g (Left x) = 
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
either-functor-composition-law f g (Right x) = 
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


-- Tree Functor

-- helper functions
tree-right : {A : Set} → A → Tree A → Tree A → Tree A
tree-right x l r = Node x l r

tree-left : {A : Set} → A → Tree A → Tree A → Tree A
tree-left x r l = Node x l r

tree-functor-id-law : {A : Set} (y : Tree A) → fmap id y ≡ y
tree-functor-id-law Leaf = 
    begin
        fmap id Leaf
    =⟨⟩ -- applying fmap
        Leaf
    end
tree-functor-id-law (Node x l r) =
    begin
        fmap id (Node x l r)
    =⟨⟩ -- applying fmap
        Node (id x) (fmap id l) (fmap id r)
    =⟨⟩ -- applying id
        Node x (fmap id l) (fmap id r)
    =⟨ cong (tree-left x (fmap id r)) (tree-functor-id-law l) ⟩
        Node x l (fmap id r)
    =⟨ cong (tree-right x l) (tree-functor-id-law r) ⟩
        Node x l r
    end

tree-functor-composition-law : {A B C : Set} (f : B → C) → (g : A → B) → (x : Tree A) → fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x
tree-functor-composition-law f g Leaf =
    begin
        fmap (f ∘ g) Leaf
    =⟨⟩ -- applying fmap
        Leaf
    =⟨⟩ -- unapplying fmap
        fmap f Leaf
    =⟨⟩ -- unapplying fmap
        fmap f (fmap g Leaf)
    =⟨⟩ -- unapplying ∘
        (fmap f ∘ fmap g) Leaf
    end
tree-functor-composition-law f g (Node x l r) = 
    begin
        fmap (f ∘ g) (Node x l r)
    =⟨⟩ -- applying fmap
        Node ((f ∘ g) x) (fmap (f ∘ g) l) (fmap (f ∘ g) r)
    =⟨⟩ -- applying ∘
        Node (f (g x)) (fmap (f ∘ g) l) (fmap (f ∘ g) r)
    =⟨ cong (tree-left (f (g x)) (fmap (f ∘ g) r)) (tree-functor-composition-law f g l) ⟩
        Node (f (g x)) ((fmap f ∘ fmap g) l) (fmap (f ∘ g) r)
    =⟨ cong (tree-right (f (g x)) ((fmap f ∘ fmap g) l)) (tree-functor-composition-law f g r) ⟩
        Node (f (g x)) ((fmap f ∘ fmap g) l) ((fmap f ∘ fmap g) r)
    =⟨⟩ -- unapplying ∘
        Node ((f ∘ g) x) ((fmap f ∘ fmap g) l) ((fmap f ∘ fmap g) r)
    =⟨⟩ -- unapplying fmap
        (fmap f ∘ fmap g) (Node x l r)
    end
