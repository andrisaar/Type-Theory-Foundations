
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

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {σ} → Var Γ σ → Var Δ σ 

wk : ∀{Γ Δ σ} → Ren Γ Δ → Ren (Γ ∷ σ) (Δ ∷ σ)
wk f vz     = vz
wk f (vs i) = vs (f i)

ren : ∀{Γ Δ} → Ren Γ Δ → ∀ {σ} → Tm Γ σ → Tm Δ σ
ren f (var x)   = var (f x)
ren f (t $ u)   = (ren f t) $ (ren f u)
ren f (lam t)   = lam (ren (wk f) t)

Sub : Ctx → Ctx → Set
Sub Γ Δ = ∀{σ} → Var Γ σ → Tm Δ σ

lift : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ ∷ σ) (Δ ∷ σ)
lift f vz     = var vz
lift f (vs x) = ren vs_ (f x)

extend : ∀{Γ Δ σ} → Sub Γ Δ → Tm Δ σ → Sub (Γ ∷ σ) Δ
extend f t vz = t
extend f t (vs y) = f y

sub : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub f (var x)   = f x
sub f (t $ u)   = (sub f t) $ (sub f u)
sub f (lam t)   = lam (sub (lift f) t)

sub₁ : ∀{Γ σ τ} → Tm Γ σ → Tm (Γ ∷ σ) τ → Tm Γ τ
sub₁ N M = sub (extend var_ N) M

_∘_ : {A : Set}{B : A → Set}{C : (a : A) → B a → Set} → 
      (∀{a} b → C a b) → (g : (∀ a → B a)) → ∀ a → C a (g a)
f ∘ g = λ a → f (g a)

subComp : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
subComp f g = sub f ∘ g

-- time for the mysterious four lemmas:
renComp : ∀{B Γ Δ} → Ren Γ Δ → Ren B Γ → Ren B Δ
renComp f g = f ∘ g

wkcomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B ∷ σ) τ) → 
            wk (renComp f g) x ≡ renComp (wk f) (wk g) x  
wkcomp f g vz     = refl
wkcomp f g (vs i) = refl

rencomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
            ren (renComp f g) t ≡ (ren f ∘ ren g) t
rencomp f g (var x) = refl
rencomp f g (t $ u) = cong₂ _$_ (rencomp f g t) (rencomp f g u)
rencomp f g (lam t) = cong lam_ (trans (cong (λ (f : Ren _ _) → ren f t)
                                              (iext λ _ → ext (wkcomp f g)))
                                        (rencomp (wk f) (wk g) t))

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

subId : ∀{Γ} → Sub Γ Γ
subId = var_

liftid : ∀{Γ σ τ}(x : Var (Γ ∷ σ) τ) → lift subId x ≡ subId x
liftid vz     = refl
liftid (vs x) = refl

id : {A : Set} → A → A
id a = a

subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≡ id t
subid (var x)   = refl
subid (t $ u)   = cong₂ _$_ (subid t) (subid u)
subid (lam t)   = cong lam_ (trans (cong (λ (f : Sub _ _) → sub f t) 
                                        (iext λ _ → ext liftid)) 
                                  (subid t))
-- back to our regular programming

subcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) → 
          sub (subComp f g) t ≡ (sub f ∘ sub g) t
subcomp f g (var x) = refl
subcomp f g (t $ u) = cong₂ _$_ (subcomp f g t) (subcomp f g u) 
subcomp f g (lam t) = cong lam_ (trans (cong (λ (f : Sub _ _) → sub f t) (iext λ _ → ext (liftcomp f g))) (subcomp (lift f) (lift g) t)) 

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

hd : ∀ {Γ Δ σ} → Sub (Γ ∷ σ) Δ → Tm Δ σ
hd s = s vz

tl : ∀ {Γ Δ σ} → Sub (Γ ∷ σ) Δ → Sub Γ Δ
tl s v = s (vs v)
