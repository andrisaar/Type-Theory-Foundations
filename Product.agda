
-- mostly stolen from Agda standard library just so this could be standalone

module Product where

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

syntax Σ A (λ x → B) = Σ[ x ∶ A ] B

_×_ : (A : Set) (B : Set) → Set
A × B = Σ[ x ∶ A ] B