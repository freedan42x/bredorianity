module prop where

open import base
open import eq


Assoc : ∀ A (_∙_ : A → A → A) → Set a
Assoc _ _∙_ = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)


Comm : ∀ A (_∙_ : A → A → A) → Set a
Comm _ _∙_ = ∀ x y → x ∙ y ≡ y ∙ x
