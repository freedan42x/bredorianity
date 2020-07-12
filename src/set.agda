module set where

open import base
open import sum
open import prod as P
open import logic
open import func
open import prop
open import iso



---------------------------------
--         Definitions         --
---------------------------------


infix 4 _∈_ _∉_ _⊂_ _≣_
infix 5 _∪_ _∩_ _-_
infix 6 _′


Pred : Set a → ∀ b → Set _
Pred A b = A → Set b


∅ : Pred A 0ℓ
∅ = const ⊥


U : Pred A 0ℓ
U = const ⊤


_∈_ _∉_ : ∀ x → Pred A b → Set _
x ∈ P = P x
x ∉ P = ¬ x ∈ P


_⊂_ _≣_ : Pred A b → Pred A c → Set _
P ⊂ Q = ∀ {x} → x ∈ P → x ∈ Q
P ≣ Q = P ⊂ Q × Q ⊂ P


_∪_ _∩_ _-_ : Pred A b → Pred A c → Pred A _
P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q
P ∩ Q = λ x → x ∈ P × x ∈ Q
P - Q = λ x → x ∈ P × x ∉ Q


_′ : Pred A b → Pred A _
P ′ = λ x → x ∉ P



---------------------------------
--    Equivalence Relation     --
---------------------------------


private
  variable
    P Q R : Pred A b


≣-refl : P ≣ P
≣-refl = id , id


≣-sym : P ≣ Q → Q ≣ P
≣-sym = P.swap


≣-trans : P ≣ Q → Q ≣ R → P ≣ R
≣-trans (P→Q , Q→P) (Q→R , R→Q) = Q→R ∘ P→Q , Q→P ∘ R→Q



---------------------------------
--         ≣-Reasoning         --
---------------------------------


infix  1 ≣-begin_
infixr 2 _≣⟨⟩_ _≣⟨_⟩_
infix  3 _≣-∎


≣-begin_ : {P Q : Pred A b} → P ≣ Q → P ≣ Q 
≣-begin_ = id


_≣⟨_⟩_ : {P Q R : Pred A b} → Pred A b → P ≣ Q → Q ≣ R → P ≣ R
_≣⟨_⟩_ = λ _ → ≣-trans


_≣⟨⟩_ : {P Q : Pred A b} → Pred A b → P ≣ Q → P ≣ Q
_≣⟨⟩_ = const id


_≣-∎ : Pred A b → P ≣ P
_ ≣-∎ = ≣-refl



---------------------------------
--         Properties          --
---------------------------------


∉-∅ : (x : A) → x ∉ ∅
∉-∅ _ ()


∈-U : (x : A) → x ∈ U
∈-U _ = tt



∪-assoc : {A : Set a} → AssocR {A = Pred A b} _≣_ _∪_
∪-assoc P Q R =
  ≣-begin
    (P ∪ Q) ∪ R
  ≣⟨⟩
    (λ x → x ∈ P ⊎ x ∈ Q) ∪ R
  ≣⟨⟩
    (λ x → (P x ⊎ Q x) ⊎ R x)
  ≣⟨ {!!} ⟩
    {!!}
  ≣⟨ {!!} ⟩
    P ∪ (Q ∪ R)
  ≣-∎


{-
∪-assoc : {A : Set a} → AssocR {A = Pred A b} _≡_ _∪_
∪-assoc P Q R =
  (λ where
    (inj₁ (inj₁ Px)) → inj₁ Px
    (inj₁ (inj₂ Qx)) → inj₂ (inj₁ Qx)
    (inj₂ Rx) → inj₂ (inj₂ Rx)) ,
  (λ where
    (inj₁ Px) → inj₁ (inj₁ Px)
    (inj₂ (inj₁ Qx)) → inj₁ (inj₂ Qx)
    (inj₂ (inj₂ Rx)) → inj₂ Rx)

-}


--∩-assoc : {A : Set a} → AssocR {A = Pred A b} _≡_ _∩_
--∩-assoc P Q R =
--  (λ x → {!!}) ,
--  {!!}
