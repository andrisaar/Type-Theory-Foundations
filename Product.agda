
-- mostly stolen from Agda standard library just so this could be standalone

module Product where

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

_×_ : (A : Set) (B : Set) → Set
A × B = Σ[ x ∶ A ] B

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B