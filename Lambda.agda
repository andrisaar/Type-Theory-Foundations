module Lambda where
open import Equality

data Unit : Set where
  <>    : Unit

data Ty : Set where
  ℕ     : Ty
  Bool  : Ty
  _⟶_  : Ty → Ty → Ty

data Ctx : Set where
  ∅   : Ctx
  _∷_ : Ctx → Ty → Ctx

data Var : Ctx → Ty → Set where
  vz  : ∀ {Γ σ} → Var (Γ ∷ σ) σ
  vs_ : ∀ {Γ σ τ} → Var Γ σ → Var (Γ ∷ τ) σ 
  
data Tm : Ctx → Ty → Set where
  var_ : ∀ {Γ σ} → Var Γ σ → Tm Γ σ
  _$_  : ∀ {Γ σ τ} → Tm Γ (σ ⟶ τ) → Tm Γ σ → Tm Γ τ
  lam_ : ∀ {Γ σ τ} → Tm (Γ ∷ σ) τ → Tm Γ (σ ⟶ τ)

