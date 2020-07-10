module eq where

open import base
open import Relation.Binary.PropositionalEquality public
open ≡-Reasoning public



postulate
  fun-ext : ∀ {b} {B : A → Set b} {f g : ∀ x → B x}
          → (∀ x → f x ≡ g x)
          → f ≡ g
