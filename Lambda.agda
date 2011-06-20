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

infixl 10 _∷_

data Var : Ctx → Ty → Set where
  vz : ∀ {Γ σ} → Var (Γ ∷ σ) σ
  vs : ∀ {Γ σ τ} → Var Γ σ → Var (Γ ∷ τ) σ 
  
data Tm : Ctx → Ty → Set where
  var  : ∀ {Γ σ} → Var Γ σ → Tm Γ σ
  _&_  : ∀ {Γ σ τ} → Tm Γ (σ ⟶ τ) → Tm Γ σ → Tm Γ τ
  lam  : ∀ {Γ σ τ} → Tm (Γ ∷ σ) τ → Tm Γ (σ ⟶ τ)
  zero : ∀{Γ} → Tm Γ ℕ
  suc  : ∀{Γ} → Tm Γ ℕ → Tm Γ ℕ
  rec  : ∀{Γ σ} → Tm Γ ℕ → Tm Γ σ → Tm (Γ ∷ ℕ ∷ σ) σ → Tm Γ σ
