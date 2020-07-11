module eq where

open import base
open import func
open import Relation.Binary.PropositionalEquality public
open ≡-Reasoning public


private
  variable
    P : A → Set b
    f g : ∀ x → P x



postulate
  fun-ext : (∀ x → f x ≡ g x) → f ≡ g


cong-sym : ∀ {x y} {f : A → B} (p : x ≡ y) → cong f (sym p) ≡ sym (cong f p)
cong-sym refl = refl
