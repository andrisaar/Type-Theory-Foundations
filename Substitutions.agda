module Substitutions where

open import Equality
open import Lambda
open import Renamings

Sub : Ctx → Ctx → Set
Sub Γ Δ = ∀{σ} → Var Γ σ → Tm Δ σ

lift : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ ∷ σ) (Δ ∷ σ)
lift f vz     = var vz
lift f (vs x) = ren vs_ (f x)

sub : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub f (var x)   = f x
sub f (t $ u)   = (sub f t) $ (sub f u)
sub f (lam t)   = lam (sub (lift f) t)

subId : ∀{Γ} → Sub Γ Γ
subId = var_

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
subren f g (lam t)   = cong lam_ (trans (subren (lift f) (wk g) t)
                                       (cong (λ (f : Sub _ _) → sub f t) 
                                             (iext λ _ → ext (liftwk f g))))

renwklift : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B ∷ σ) τ) →
               (ren (wk f) ∘ lift g) x ≡ lift (ren f ∘ g) x
renwklift f g vz     = refl
renwklift f g (vs x) = trans (sym (rencomp (wk f) vs_ (g x))) 
                                (rencomp vs_ f (g x))

rensub : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) →
         (ren f ∘ sub g) t ≡ sub (ren f ∘ g) t
rensub f g (var x) = refl
rensub f g (t $ u) = cong₂ _$_ (rensub f g t) (rensub f g u)
rensub f g (lam t) = cong lam_ (trans (rensub (wk f) (lift g) t) 
                                       (cong (λ (f : Sub _ _) → sub f t) 
                                             (iext λ _ → 
                                               ext (renwklift f g))))

liftcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B ∷ σ) τ) →
           lift (subComp f g) x ≡ subComp (lift f) (lift g) x
liftcomp f g vz     = refl
liftcomp f g (vs x) = trans (rensub vs_ f (g x))
                            (sym (subren (lift f) vs_ (g x)))

liftid : ∀{Γ σ τ}(x : Var (Γ ∷ σ) τ) → lift subId x ≡ subId x
liftid vz     = refl
liftid (vs x) = refl

subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≡ id t
subid (var x)   = refl
subid (t $ u)   = cong₂ _$_ (subid t) (subid u)
subid (lam t)   = cong lam_ (trans (cong (λ (f : Sub _ _) → sub f t) 
                                        (iext λ _ → ext liftid)) 
                                  (subid t))

subcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) → 
          sub (subComp f g) t ≡ (sub f ∘ sub g) t
subcomp f g (var x) = refl
subcomp f g (t $ u) = cong₂ _$_ (subcomp f g t) (subcomp f g u) 
subcomp f g (lam t) = cong lam_ (trans (cong (λ (f : Sub _ _) → sub f t) (iext λ _ → ext (liftcomp f g))) (subcomp (lift f) (lift g) t)) 

--that was the basic machinery, here are some modern conveniences like one place sub

_::_ : ∀{Γ Δ σ} → Sub Γ Δ → Tm Δ σ → Sub (Γ ∷ σ) Δ
(f :: t) vz = t
(f :: t) (vs y) = f y

sub₁ : ∀{Γ σ τ} → Tm Γ σ → Tm (Γ ∷ σ) τ → Tm Γ τ
sub₁ N M = sub (subId :: N) M

hd : ∀ {Γ Δ σ} → Sub (Γ ∷ σ) Δ → Tm Δ σ
hd s = s vz

tl : ∀ {Γ Δ σ} → Sub (Γ ∷ σ) Δ → Sub Γ Δ
tl s v = s (vs v)

-- we need this lemma for one place subs in beta reduction
lemma2 : ∀{Γ Δ σ u ρ} {γ : Sub Γ Δ} → (a : Var (Γ ∷ σ) ρ) → (γ :: u) a ≡ sub (subId :: u) (lift γ a)
lemma2 vz = refl
lemma2 {γ = γ} (vs x) = trans (cong₂ (λ f x → f x) (sym (ext subid)) refl) (sym (subren (subId :: _) vs_ (γ x)))

lemma : ∀{Γ Δ σ τ} → (u : Tm Δ σ) → (y : Tm (Γ ∷ σ) τ) → {γ : Sub Γ Δ} → (sub (γ :: u) y) ≡  (sub (subId :: u) ∘ sub (lift γ)) y
lemma u y {γ} = trans (cong (λ (f : Sub _ _) → sub f y) (iext λ _ → ext lemma2) ) (subcomp (subId :: u) (lift γ) y)
