module Renamings where

open import Relation.Binary.PropositionalEquality
open import Equality
open import Lambda
open import Data.Product
open import Function

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {σ} → Var Γ σ → Var Δ σ 

wk : ∀{Γ Δ σ} → Ren Γ Δ → Ren (Γ ∷ σ) (Δ ∷ σ)
wk f vz     = vz
wk f (vs i) = vs (f i)

ren : ∀{Γ Δ} → Ren Γ Δ → ∀ {σ} → Tm Γ σ → Tm Δ σ
ren f (var x)   = var (f x)
ren f (t & u)   = (ren f t) & (ren f u)
ren f (lam t)   = lam (ren (wk f) t)
ren f zero      = zero
ren f (suc n)   = suc (ren f n)
ren f (rec n mz ms) = rec (ren f n) (ren f mz) (ren (wk (wk f)) ms)

renComp : ∀{B Γ Δ} → Ren Γ Δ → Ren B Γ → Ren B Δ
renComp f g = f ∘ g

-- we check the second functor laws for wk and ren, the first one isn't needed.
wkcomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B ∷ σ) τ) → 
            wk (renComp f g) x ≡ renComp (wk f) (wk g) x  
wkcomp f g vz     = refl
wkcomp f g (vs i) = refl

rencomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
            ren (renComp f g) t ≡ (ren f ∘ ren g) t
rencomp f g (var x) = refl
rencomp f g (t & u) = cong₂ _&_ (rencomp f g t) (rencomp f g u)
rencomp f g (lam t) = cong lam (trans (cong (λ (f : Ren _ _) → ren f t)
                                              (iext λ _ → ext (wkcomp f g)))
                                        (rencomp (wk f) (wk g) t))
rencomp f g zero = refl
rencomp f g (suc n) = cong suc (rencomp f g n)
rencomp f g (rec n mz ms) = cong₃ rec (rencomp f g n) (rencomp f g mz) (trans (cong (λ (f : Ren _ _) → ren f ms) (iext λ _ → ext (λ v → trans (cong (λ (f : Ren _ _) → wk f v) (iext λ _ → ext (wkcomp f g))) (wkcomp (wk f) (wk g) v)))) (rencomp (wk (wk f)) (wk (wk g)) ms))
 
