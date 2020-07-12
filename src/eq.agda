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
  fun-extR : (_~_ : ∀ {a} {A : Set a} → A → A → Set a) → (∀ x → f x ~ g x) → f ~ g


fun-ext : (∀ x → f x ≡ g x) → f ≡ g
fun-ext = fun-extR _≡_


cong-sym : ∀ {x y} {f : A → B} (p : x ≡ y) → cong f (sym p) ≡ sym (cong f p)
cong-sym refl = refl
