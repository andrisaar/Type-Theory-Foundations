
module Main where
open import Equality
open import Lambda
open import Product

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

lemma2 : ∀{Γ Δ σ u ρ} {γ : Sub Γ Δ} → (a : Var (Γ ∷ σ) ρ) → extend γ u a ≡ sub (extend var_ u) (lift γ a)
lemma2 vz = refl
lemma2 {γ = γ} (vs x) = trans (cong₂ (λ f x → f x) (sym (ext subid)) refl) (sym (subren (extend var_ _) vs_ (γ x)))

lemma : ∀{Γ Δ σ τ} → (u : Tm Δ σ) → (y : Tm (Γ ∷ σ) τ) → {γ : Sub Γ Δ} → (sub (extend γ u) y) ≡  (sub (extend var_ u) ∘ sub (lift γ)) y
lemma u y {γ} = trans (cong (λ (f : Sub _ _) → sub f y) (iext λ _ → ext lemma2) ) (subcomp (extend var_ u) (lift γ) y)

thm : ∀ {Γ Δ σ} {γ : Sub Γ Δ} → (M : Tm Γ σ) → R' Γ γ → R σ (sub γ M)
thm (var vz)     (_ , t) = t
thm (var (vs x)) (γ , _) = thm (var x) γ
thm (y $ y')     p       = thm y p (thm y' p)
thm {σ = σ ⟶ τ} {γ = γ} (lam y) p = λ {u} p' → headexp (β (sub (lift _) y) u) (subst (R τ) (lemma u y) (thm {γ = extend γ u} y (p , p')))

