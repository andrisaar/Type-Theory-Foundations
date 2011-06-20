
module Main where
open import Equality
open import Lambda
open import Utils
open Σ
open import Renamings
open import Substitutions

mutual
  data _value : ∀{Γ σ} → Tm Γ σ → Set where
    vlam : ∀ {Γ σ τ} → (m : Tm (Γ ∷ σ) τ) →
      (lam m) value
    vzero : ∀{Γ} → zero {Γ} value
    vsuc : ∀{Γ}(m : Tm Γ ℕ) → suc m value

data _⇒_ : ∀{Γ σ} → Tm Γ σ → Tm Γ σ → Set where
 β    : ∀{Γ σ τ}{M : Tm (Γ ∷ σ) τ}{N : Tm Γ σ} → 
        ((lam M) $ N) ⇒ sub₁ N M
 cong$ : ∀ {Γ σ τ} {M : Tm Γ (σ ⟶ τ)} {M' N} → M ⇒ M' →
        (M $ N) ⇒ (M' $ N)
 congsuc : ∀{Γ}{M M' : Tm Γ ℕ} → M ⇒ M' → suc M ⇒ suc M'
 congrec : ∀{Γ σ}(n n' : Tm Γ ℕ) → n ⇒ n' → 
           {mz : Tm Γ σ}{ms : Tm (Γ ∷ ℕ ∷ σ) σ} → rec n mz ms ⇒ rec n' mz ms
 reczero : ∀{Γ σ}{mz : Tm Γ σ}{ms : Tm (Γ ∷ ℕ ∷ σ) σ} → rec zero mz ms ⇒ mz
 recsuc  : ∀{Γ σ}{n : Tm Γ ℕ}{mz : Tm Γ σ}{ms : Tm (Γ ∷ ℕ ∷ σ) σ} → 
          rec (suc n) mz ms ⇒ sub (subId :: n :: rec n mz ms) ms

data _⇒*_ : ∀{Γ σ} → Tm Γ σ → Tm Γ σ → Set where
  refl⇒ : ∀ {Γ σ} {c : Tm Γ σ} → c ⇒* c
  trans⇒ : ∀ {Γ σ} {c : Tm Γ σ} {c' c''} → 
    c ⇒ c' → c' ⇒* c'' → 
    c ⇒* c''

congrec* : ∀{Γ σ}{n n' : Tm Γ ℕ} → n ⇒* n' → 
           {mz : Tm Γ σ}{ms : Tm (Γ ∷ ℕ ∷ σ) σ} → rec n mz ms ⇒* rec n' mz ms
congrec* refl⇒ = refl⇒
congrec* (trans⇒ p p') = trans⇒ (congrec _ _ p) (congrec* p')

data RN : Tm ∅ ℕ → Set where
  rz : ∀{t} → t ⇒* zero → RN t 
  rs : ∀{t t'} → t ⇒* suc t' → RN t' →  RN t

R : (σ : Ty) → Tm ∅  σ → Set
R ℕ t = RN t
R Bool      t = Unit
R (σ ⟶ τ) t = ∀ {u} → R σ u → R τ (t $ u)

R' : (Γ : Ctx) → Sub Γ ∅ → Set
R' ∅       p = Unit
R' (Γ ∷ σ) p = R' Γ (tl p) × R σ (hd p)

headexp : ∀{σ} {M N : Tm ∅ σ} → M ⇒ N → R σ N → R σ M
headexp {ℕ} p (rz q) = rz (trans⇒ p q)
headexp {ℕ} p (rs q q') = rs (trans⇒ p q) q'
headexp {Bool}    p q = q
headexp {σ ⟶ τ} p q = λ {u} p' → headexp {τ} (cong$ p) (q {u} p')

headexp* : ∀{σ} {M N : Tm ∅ σ} → M ⇒* N → R σ N → R σ M
headexp* refl⇒ q = q
headexp* (trans⇒ p p') q = headexp p (headexp* p' q)

P : (n : Tm ∅ ℕ)(σ : Ty)(mz : Tm ∅ σ)(ms : Tm (∅ ∷ ℕ ∷ σ) σ) → Set
P n σ mz ms =  R ℕ n × R σ (rec n mz ms)

closedP : ∀ {n σ mz ms} → R σ mz → 
       (∀ {k} → R ℕ k → ∀{t} → R σ t → R σ (sub (subId :: k :: t) ms)) → 
       (n ⇒* zero) ∨ Σ (Tm ∅ ℕ) (λ n' → (n ⇒* suc n') × P n' σ mz ms)  → 
       P n σ mz ms
closedP p f (inl pz) = rz pz , headexp* (congrec* pz) (headexp reczero p) 
closedP p f (inr (n' , (q , (q' , q'')))) = 
  rs q q' , headexp* (congrec* q) (headexp recsuc (f q' q''))

lem : ∀{σ}{n} → RN n → ∀ {mz ms} →  R σ mz → 
      (∀ {k} → R ℕ k → ∀{t} → R σ t → R σ (sub (subId :: k :: t) ms)) →  
      P n σ mz ms
lem (rz p)    q f = closedP q f (inl p) 
lem (rs p p') q f = closedP q f (inr (_ , (p , lem p' q f)))

thm : ∀ {Γ σ} {γ : Sub Γ ∅} → (M : Tm Γ σ) → R' Γ γ → R σ (sub γ M)
thm (var vz)     (_ , t) = t
thm (var (vs x)) (γ , _) = thm (var x) γ
thm (t $ u)     p       = thm t p (thm u p)
thm (lam t) p = λ {u} p' → 
  headexp β (subst (R _) (lemma u t) (thm t (p , p')))
thm zero p  = rz refl⇒
thm (suc n) p = rs refl⇒ (thm n p)
thm (rec n mz ms) p = snd (lem x y (λ x y → 
  subst (R _) (sym (lemma3 _ _ _ ms)) (thm ms ((p , x) , y)) ))
  where x = thm n p
        y = thm mz p

_⇓ : ∀{σ} → Tm ∅ σ → Set 
_⇓ {σ} t = Σ (Tm ∅ σ) λ t' → (t ⇒* t') × t' value
      
term : (t : Tm ∅ ℕ) → t ⇓
term t with subst RN (subid t) (thm {∅}{ℕ}{subId} t <>)
term t | rz p    = zero , (p , vzero)
term t | rs p p' = suc _ , ((p , vsuc _))