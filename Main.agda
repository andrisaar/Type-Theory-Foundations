
module Main where
open import Equality
open import Lambda
open import Product
open import Renamings
open import Substitutions

mutual
  data _value : ∀{Γ σ} → Tm Γ σ → Set where
    vlam : ∀ {Γ σ τ} → (m : Tm (Γ ∷ σ) τ) →
      (lam m) value
    vn : ∀ {Γ σ} {t : Tm Γ σ} → t neutral → 
      t value

  data _neutral : ∀{Γ σ} → Tm Γ σ → Set where
    nvar : ∀ {Γ σ} → (v : Var Γ σ) →
      (var v) neutral
    napp : ∀ {Γ σ τ} → (n : Tm Γ (σ ⟶ τ)) → (m : Tm Γ σ) → n neutral →
      (n $ m) neutral


data _⇒_ : ∀{Γ σ} → Tm Γ σ → Tm Γ σ → Set where
 β    : ∀{Γ σ τ} → (M : Tm (Γ ∷ σ) τ) → (N : Tm Γ σ) → 
        ((lam M) $ N) ⇒ sub₁ N M
 c    : ∀ {Γ σ τ} {M : Tm Γ (σ ⟶ τ)} {M' N} → M ⇒ M' →
        (M $ N) ⇒ (M' $ N)

data _⇒*_ : ∀{Γ σ} → Tm Γ σ → Tm Γ σ → Set where
  Finish : ∀ {Γ σ} {c : Tm Γ σ} → c ⇒* c
  Step   : ∀ {Γ σ} {c : Tm Γ σ} {c' c''} → 
    c ⇒ c' → c' ⇒* c'' → 
    c ⇒* c''


R : {Γ : Ctx} → (σ : Ty) → Tm Γ σ → Set
R ℕ         t = Unit
R Bool      t = Unit
R (σ ⟶ τ) t = ∀ {u} → R σ u → R τ (t $ u)

headexp : ∀{σ Γ} {M N : Tm Γ σ} → M ⇒ N → R σ N → R σ M
headexp {ℕ}       p q = q
headexp {Bool}    p q = q
headexp {σ ⟶ τ} p q = λ {u} p' → headexp {τ} (c p) (q {u} p')

R' : (Γ : Ctx) → {Δ : Ctx} → Sub Γ Δ → Set
R' ∅       p = Unit
R' (Γ ∷ σ) p = R' Γ (tl p) × R σ (hd p)

thm : ∀ {Γ Δ σ} {γ : Sub Γ Δ} → (M : Tm Γ σ) → R' Γ γ → R σ (sub γ M)
thm (var vz)     (_ , t) = t
thm (var (vs x)) (γ , _) = thm (var x) γ
thm (y $ y')     p       = thm y p (thm y' p)
thm {σ = σ ⟶ τ} {γ = γ} (lam y) p = λ {u} p' → headexp (β (sub (lift _) y) u) (subst (R τ) (lemma u y) (thm {γ = γ :: u} y (p , p')))

