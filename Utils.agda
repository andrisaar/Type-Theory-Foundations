
-- mostly stolen from Agda standard library just so this could be standalone

module Utils where

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

_×_ : (A : Set) (B : Set) → Set
A × B = Σ A λ _ → B

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

_∘_ : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} → 
      (∀{a} b → C a b) → (g : (∀ a → B a)) → ∀ a → C a (g a)
f ∘ g = λ a → f (g a)

id : {A : Set} → A → A
id a = a
