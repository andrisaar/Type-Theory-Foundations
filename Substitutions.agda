module Substitutions where

open import Equality
open import Lambda
open import Renamings

Sub : Ctx → Ctx → Set
Sub Γ Δ = ∀{σ} → Var Γ σ → Tm Δ σ

lift : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ ∷ σ) (Δ ∷ σ)
lift f vz     = var vz
lift f (vs x) = ren vs (f x)

sub : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub f (var x)   = f x
sub f (t $ u)   = (sub f t) $ (sub f u)
sub f (lam t)   = lam (sub (lift f) t)
sub f zero      = zero
sub f (suc n)   = suc (sub f n)
sub f (rec n mz ms) = rec (sub f n) (sub f mz) (sub (lift (lift f)) ms)

subId : ∀{Γ} → Sub Γ Γ
subId = var

subComp : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
subComp f g = sub f ∘ g

-- we have now given the operations for a category of subs and a functor from there to the category of terms. Next we need to check they laws of a category and a functor


liftwk : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B ∷ σ) τ) →
            (lift f ∘ wk g) x ≡ lift (f ∘ g) x
liftwk f g vz     = refl
liftwk f g (vs x) = refl


subren : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
         (sub f ∘ ren g) t ≡ sub (f ∘ g) t
subren f g (var x)   = refl
subren f g (t $ u)   = cong₂ _$_ (subren f g t) (subren f g u)
subren f g (lam t)   = cong lam (trans (subren (lift f) (wk g) t)
                                       (cong (λ (f : Sub _ _) → sub f t) 
                                             (iext λ _ → ext (liftwk f g))))
subren f g zero          = refl
subren f g (suc n)       = cong suc (subren f g n)
subren f g (rec n mz ms) = cong₃ rec (subren f g n) (subren f g mz) (trans (subren (lift (lift f)) (wk (wk g)) ms) (cong (λ (f : Sub _ _) → sub f ms) (iext λ _ → ext (λ x → trans (liftwk (lift f) (wk g) x) (cong (λ (f : Sub _ _) → lift f x) (iext λ _ → ext (liftwk f g)))))))


renwklift : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B ∷ σ) τ) →
               (ren (wk f) ∘ lift g) x ≡ lift (ren f ∘ g) x
renwklift f g vz     = refl
renwklift f g (vs x) = trans (sym (rencomp (wk f) vs (g x))) 
                                (rencomp vs f (g x))

rensub : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) →
         (ren f ∘ sub g) t ≡ sub (ren f ∘ g) t
rensub f g (var x) = refl
rensub f g (t $ u) = cong₂ _$_ (rensub f g t) (rensub f g u)
rensub f g (lam t) = cong lam (trans (rensub (wk f) (lift g) t) 
                                       (cong (λ (f : Sub _ _) → sub f t) 
                                             (iext λ _ → 
                                               ext (renwklift f g))))
rensub f g zero = refl
rensub f g (suc n) = cong suc (rensub f g n)
rensub f g (rec n mz ms) = cong₃ rec (rensub f g n) (rensub f g mz) (trans (rensub (wk (wk f)) (lift (lift g)) ms) (cong (λ (f : Sub _ _) → sub f ms) (iext λ _ → ext λ x → trans (renwklift (wk f) (lift g) x) (cong (λ (f : Sub _ _) → lift f x) (iext λ _ → ext (renwklift f g))))))

liftcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B ∷ σ) τ) →
           lift (subComp f g) x ≡ subComp (lift f) (lift g) x
liftcomp f g vz     = refl
liftcomp f g (vs x) = trans (rensub vs f (g x))
                            (sym (subren (lift f) vs (g x)))


liftid : ∀{Γ σ τ}(x : Var (Γ ∷ σ) τ) → lift subId x ≡ subId x
liftid vz     = refl
liftid (vs x) = refl


subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≡ id t
subid (var x)   = refl
subid (t $ u)   = cong₂ _$_ (subid t) (subid u)
subid (lam t)   = cong lam (trans (cong (λ (f : Sub _ _) → sub f t) 
                                        (iext λ _ → ext liftid)) 
                                  (subid t))
subid zero      = refl
subid (suc n)   = cong suc (subid n)
subid (rec n mz ms) = cong₃ rec (subid n) (subid mz) (trans (cong (λ (f : Sub _ _) → sub f ms) (iext λ _ → ext (λ x → trans (cong (λ (f : Sub _ _) → lift f x) (iext λ _ → ext liftid)) (liftid x)))) (subid ms))


subcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) → 
          sub (subComp f g) t ≡ (sub f ∘ sub g) t
subcomp f g (var x) = refl
subcomp f g (t $ u) = cong₂ _$_ (subcomp f g t) (subcomp f g u) 
subcomp f g (lam t) = cong lam (trans (cong (λ (f : Sub _ _) → sub f t) (iext λ _ → ext (liftcomp f g))) (subcomp (lift f) (lift g) t)) 
subcomp f g zero = refl
subcomp f g (suc n) = cong suc (subcomp f g n)
subcomp f g (rec n mz ms) = cong₃ rec (subcomp f g n) (subcomp f g mz) (trans (cong (λ (f : Sub _ _) → sub f ms) (iext λ _ → ext (λ x → trans (cong (λ (f : Sub _ _) → lift f x) (iext λ _ → ext (liftcomp f g))) (liftcomp (lift f) (lift g) x)))) (subcomp (lift (lift f)) (lift (lift g)) ms))

--that was the basic machinery, here are some modern conveniences like one place sub

_::_ : ∀{Γ Δ σ} → Sub Γ Δ → Tm Δ σ → Sub (Γ ∷ σ) Δ
(f :: t) vz = t
(f :: t) (vs y) = f y

infixl 10 _::_

sub₁ : ∀{Γ σ τ} → Tm Γ σ → Tm (Γ ∷ σ) τ → Tm Γ τ
sub₁ N M = sub (subId :: N) M

hd : ∀ {Γ Δ σ} → Sub (Γ ∷ σ) Δ → Tm Δ σ
hd s = s vz

tl : ∀ {Γ Δ σ} → Sub (Γ ∷ σ) Δ → Sub Γ Δ
tl s v = s (vs v)

-- we need this lemma for one place subs in beta reduction
lemma2 : ∀{Γ Δ σ u ρ} {γ : Sub Γ Δ} → (a : Var (Γ ∷ σ) ρ) → (γ :: u) a ≡ sub (subId :: u) (lift γ a)
lemma2 vz = refl
lemma2 {γ = γ} (vs x) = trans (cong₂ (λ f x → f x) (sym (ext subid)) refl) (sym (subren (subId :: _) vs (γ x)))


lemma : ∀{Γ Δ σ τ} → (u : Tm Δ σ) → (y : Tm (Γ ∷ σ) τ) → {γ : Sub Γ Δ} → (sub (γ :: u) y) ≡  (sub (subId :: u) ∘ sub (lift γ)) y
lemma u y {γ} = trans (cong (λ (f : Sub _ _) → sub f y) (iext λ _ → ext lemma2) ) (subcomp (subId :: u) (lift γ) y)

lemma4 : ∀{Γ σ τ}{k  : Tm ∅ ℕ}{t  : Tm ∅ σ}{γ : Sub Γ ∅}(x  : Var (Γ ∷ ℕ ∷ σ) τ)
 → sub (subId :: k :: t) (lift (lift γ) x) ≡ (sub (subId :: t) (lift (γ :: k) x))
lemma4 vz     = refl
lemma4 {_}{_}{_}{k}{t}{γ}(vs x) = trans (trans (subren (subId :: k :: t) vs (lift γ x)) (trans (sym (lemma2 x)) (sym (subid ((γ :: k) x))))) (sym (subren (subId :: t) vs ((γ :: k) x)))


lemma3 : ∀{Γ σ}(k : Tm ∅ ℕ)(t : Tm ∅ σ)(γ : Sub Γ ∅)(ms : Tm (Γ ∷ ℕ ∷ σ) σ) → (sub (subId :: k :: t) (sub (lift (lift γ)) ms)) ≡ (sub (γ :: k :: t) ms)
lemma3 k t γ ms = trans (sym (subcomp (subId :: k :: t) (lift (lift γ)) ms)) (cong (λ (f : Sub _ _) → sub f ms) (iext λ _ → ext (λ x → trans (lemma4 x) (sym (lemma2 {γ = γ :: k} x)))))