module EvalCtx where

-- propositional equality
data _≅_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≅ a

data Nat : Set where
  z : Nat
  s : Nat → Nat

_+_ : Nat → Nat → Nat
z   + n = n
s m + n = s (m + n)

-- object level types
data Ty : Set where
  ℕ : Ty

-- contexts are sequences of types
data Ctx : Set where
  ε : Ctx
  _<_ : Ctx → Ty → Ctx

-- well scoped and typed de Bruijn indices for variables
data Var : Ctx → Ty → Set where
  vz : ∀ {Γ σ} → Var (Γ < σ) σ
  vs : ∀ {Γ σ τ} → Var Γ σ → Var (Γ < τ) σ 

-- a well scoped and typed language of variables, natural numbers and addition
data Tm : Ctx → Ty → Set where
  var : ∀{Γ σ} → Var Γ σ → Tm Γ σ
  num : ∀{Γ} → Nat → Tm Γ ℕ
  plus : ∀{Γ} → Tm Γ ℕ → Tm Γ ℕ → Tm Γ ℕ

-- typed evaluation contexts, typed by what goes in the hole
data E : Ctx → Ty →  Set where
  ◦ : ∀{Γ σ} → E Γ σ 
  plusl : ∀{Γ σ} → E Γ σ → Tm Γ ℕ → E Γ σ
  plusr : ∀{Γ σ} → Tm Γ ℕ → E Γ σ → E Γ σ

-- instruction transition
data _∼>_ : ∀{Γ σ} → Tm Γ σ → Tm Γ σ → Set where
  plus∼> : ∀{Γ m n p} → (m + n) ≅ p → plus {Γ} (num m) (num n) ∼> num {Γ} p

-- inductive definition of filling in an evaluation context
data _≡_[_] : ∀{Γ Γ' σ σ'} → Tm Γ σ → E Γ' σ' → Tm Γ' σ' → Set where
  a : ∀{Γ σ}{e : Tm Γ σ} → e ≡ ◦ [ e ]
  b : ∀{Γ σ}{e₁ : Tm Γ ℕ}{E₁ : E Γ σ}{e : Tm Γ σ} → e₁ ≡ E₁ [ e ] → 
      {e₂ : Tm Γ ℕ} → 
      plus e₁ e₂ ≡ plusl E₁ e₂ [ e ]
  c : ∀{Γ σ}{e₁ : Tm Γ ℕ}{e₂ : Tm Γ ℕ}{E₂ : E Γ σ}{e : Tm Γ σ} → 
      e₂ ≡ E₂ [ e ] → 
      plus e₁ e₂ ≡ plusr e₁ E₂ [ e ]

-- contextual dynamics
data _↦c_ : ∀{Γ σ} → Tm Γ σ → Tm Γ σ → Set where
  step : ∀{Γ σ σ'}{e e' : Tm Γ σ}(E₁ : E Γ σ'){e₀ e₀' : Tm Γ σ'} → 
         e ≡ E₁ [ e₀ ] → e₀ ∼> e₀' → e' ≡ E₁ [ e₀' ] → e ↦c e'

-- structural dynamics
data _↦s_ : ∀{Γ σ} → Tm Γ σ → Tm Γ σ → Set where
  plusnum : ∀{Γ m n p} → (m + n) ≅ p → plus {Γ} (num m) (num n) ↦s num p
  plusl : ∀{Γ}{e₁ e₂ e₁' : Tm Γ ℕ} → e₁ ↦s e₁' → plus e₁ e₂ ↦s plus e₁' e₂
  plusr : ∀{Γ}{e₁ e₂ e₂' : Tm Γ ℕ} → e₂ ↦s e₂' → plus e₁ e₂ ↦s plus e₁ e₂'

-- equivalence of structural and contextual dynamics
thm1 : ∀{Γ σ}{e e' : Tm Γ σ} → e ↦s e' → e ↦c e'
thm1 (plusnum refl) = step ◦ a (plus∼> refl) a
thm1 (plusl p) with thm1 p
... | step E₁ q q' q'' = step (plusl E₁ _) (b q) q' (b q'')
thm1 (plusr p) with thm1 p
... | step E₁ q q' q'' = step (plusr _ E₁) (c q) q' (c q'')

thm2 : ∀{Γ σ}{e e' : Tm Γ σ} → e ↦c e' → e ↦s e'
thm2 (step .◦ a (plus∼> p) a) = plusnum p
thm2 (step .(plusl _ _) (b y) (plus∼> p) (b y')) = 
  plusl (thm2 (step _ y (plus∼> p) y'))
thm2 (step .(plusr _ _) (c  y) (plus∼> p) (c y')) =
  plusr (thm2 (step _ y (plus∼> p) y'))
