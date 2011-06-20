--
-- Propositional equality, James' flavour, mostly stolen from his previous work
--

module Equality where

data _≡_ {A : Set} : {A' : Set} → A → A' → Set where
  refl : {a : A} → a ≡ a
  
infix 10 _≡_

trans : ∀{A A' A''}{a : A}{a' : A'}{a'' : A''} → a ≡ a' → a' ≡ a'' → a ≡ a''
trans refl p = p

sym : ∀{A A'}{a : A}{a' : A'} → a ≡ a' → a' ≡ a
sym refl = refl

cong : ∀{A}{B : A → Set}(f : ∀ a → B a){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

cong₂ : ∀{A}{B : A → Set}{C : (x : A) → B x → Set}(f : (x : A)(y : B x) → C x y){a a' : A} → a ≡ a' → {b : B a}{b' : B a'} → b ≡ b' → f a b ≡ f a' b'
cong₂ f refl refl = refl

cong₃ : ∀{A}{B : A → Set}{C : (x : A) → B x → Set}{D : (x : A)(y : B x)(z : C x y) → Set}(f : (x : A)(y : B x)(z : C x y) → D x y z){a a' : A} → a ≡ a' → {b : B a}{b' : B a'} → b ≡ b' → {c : C a b}{c' : C a' b'} → c ≡ c' → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

subst : ∀{A}(P : A → Set){a a' : A} → a ≡ a' → P a → P a'
subst P refl p = p

postulate ext : {A : Set}{B : A → Set}{f : ∀ a → B a}{g : ∀ a → B a} → 
                (∀ a → f a ≡ g a) → f ≡ g

-- this could just be derived from ext
postulate iext : {A : Set}{B : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B a} → (∀ a → f {a} ≡ g {a}) → 
                 _≡_ { {a : A} → B a}{ {a : A} → B a} f g

