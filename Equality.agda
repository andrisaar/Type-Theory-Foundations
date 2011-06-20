--
-- Propositional equality, James' flavour, mostly stolen from his previous work
--

module Equality where

open import Relation.Binary.PropositionalEquality

cong₃ : ∀{A B C D : Set}(f : A → B → C → D){x y u v p q} → 
        x ≡ y → u ≡ v → p ≡ q →  f x u p ≡ f y v q
cong₃ f refl refl refl = refl

open import Level

postulate ext : Extensionality zero zero

-- this could just be derived from ext
postulate iext : {A : Set}{B : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B a} →
                 (∀ a → f {a} ≡ g {a}) → _≡_ {zero}{ {a : A} → B a } f g
