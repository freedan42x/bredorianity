module prop where

open import base
open import eq
open import prod
open import func



---------------------------------
--         Definitions         --
---------------------------------


Assoc : ∀ A (_∙_ : A → A → A) → Set a
Assoc _ _∙_ = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)


Comm : ∀ A (_∙_ : A → A → A) → Set a
Comm _ _∙_ = ∀ x y → x ∙ y ≡ y ∙ x


Inj : (A → B) → Set _
Inj f = ∀ x y → f x ≡ f y → x ≡ y


Surj : (A → B) → Set _
Surj f = ∀ y → ∃[ x ] (y ≡ f x)


Bij : (A → B) → Set _
Bij f = Inj f × Surj f


record Inv {A : Set a} {B : Set b} (f : A → B) : Set (ℓmax a b) where
  constructor mkInv
  field
    g : B → A
    proof : ∀ x → x ≡ g (f x)


record _⇔_ (A : Set a) (B : Set b) : Set (ℓmax a b) where
  constructor mkBij
  field
    to : A → B
    inv : Inv to
    proof : Bij to × Bij (Inv.g inv)
    


---------------------------------
--         Properties          --
---------------------------------


Bij-id : Bij {B = A} id
Bij-id = (λ _ _ x=y → x=y) , _, refl
