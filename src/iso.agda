module iso where

open import base
open import eq
open import func
open import prop
open import sum as S
open import prod as P
open import logic
open import maybe as M



---------------------------------
--         Definitions         --
---------------------------------


infix 1 _≃_


record _≃_ (A : Set a) (B : Set b) : Set (ℓmax a b) where
  constructor mkIso
  field
    to : A → B
    from : B → A
    from∘to : ∀ x → x ≡ from (to x)
    to∘from : ∀ y → y ≡ to (from y)



---------------------------------
--         Properties          --
---------------------------------


≃-refl : A ≃ A
≃-refl = mkIso id id (λ _ → refl) (λ _ → refl)


≃-sym : A ≃ B → B ≃ A
≃-sym (mkIso to from from∘to to∘from)
  = mkIso from to to∘from from∘to


≃-trans : A ≃ B → B ≃ C → A ≃ C
≃-trans (mkIso A→B B→A A→eq B→eq) (mkIso B→C C→B B→eq' C→eq)
  = mkIso
  (B→C ∘ A→B)
  (B→A ∘ C→B)
  (λ x →
    begin
      x
    ≡⟨ A→eq x ⟩
      B→A (A→B x)
    ≡⟨ cong B→A (B→eq' (A→B x)) ⟩
      B→A (C→B (B→C (A→B x)))
    ∎)
  (λ y →
    begin
      y
    ≡⟨ C→eq y ⟩
      B→C (C→B y)
    ≡⟨ cong B→C (B→eq (C→B y)) ⟩
      B→C (A→B (B→A (C→B y)))
    ∎)


≡→≃ : A ≡ B → A ≃ B
≡→≃ refl = ≃-refl


≃→⇔ : A ≃ B → A ⇔ B
≃→⇔ (mkIso to from from∘to to∘from) = mkBij
  to
  (mkInv from from∘to)
  (((λ x y toX=toY →
    begin
      x
    ≡⟨ from∘to x ⟩
      from (to x)
    ≡⟨ cong from toX=toY ⟩
      from (to y)
    ≡⟨ sym (from∘to y) ⟩
      y
    ∎) , λ y → from y , to∘from y) ,
  (λ x y fromX=fromY →
    begin
      x
    ≡⟨ to∘from x ⟩
      to (from x)
    ≡⟨ cong to fromX=fromY ⟩
      to (from y)
    ≡⟨ sym (to∘from y) ⟩
      y
    ∎) , λ y → to y , from∘to y)


⇔→≃ : A ⇔ B → A ≃ B
⇔→≃ (mkBij to (mkInv from from∘to) ((_ , to-surj) , _)) = mkIso
  to
  from
  from∘to
  (λ y →
    begin
      y
    ≡⟨ proj₂ (to-surj y) ⟩
      to _
    ≡⟨ cong to (from∘to _) ⟩
      to (from (to _))
    ≡⟨ cong (to ∘ from) (sym (proj₂ (to-surj y))) ⟩
      to (from y)
    ∎)




{-
≃→⇔→eq : (i : A ≃ B) → ⇔→≃ (≃→⇔ i) ≡ i
≃→⇔→eq {B = B} (mkIso to from from∘to to∘from) =
  cong (mkIso to from from∘to) (fun-ext λ y →
    begin
      trans (to∘from y)
        (trans (cong to (from∘to (from y)))
         (trans (cong (to ∘ from) (sym (to∘from y))) refl))
    ≡⟨ cong (λ x → trans (to∘from y)
        (trans (cong to (from∘to (from y)))
         x)) (trans-reflʳ (cong (to ∘ from) (sym (to∘from y))))
    ⟩ trans (to∘from y)
        (trans (cong to (from∘to (from y)))
         (cong (to ∘ from) (sym (to∘from y))))
    ≡⟨ cong (λ x → trans (to∘from y)
        (trans (cong to (from∘to (from y)))
         x)) (trans (cong-sym (to∘from y)) (cong sym (helper y)))
    ⟩ trans (to∘from y)
        (trans (cong to (from∘to (from y)))
           (sym (cong to (from∘to (from y)))))
    ≡⟨ cong (λ x → trans (to∘from y) x) (trans-symʳ (cong to (from∘to (from y)))) ⟩
      trans (to∘from y) refl
    ≡⟨ trans-reflʳ (to∘from y) ⟩
      to∘from y
    ∎)
  where
    owo : (y : B) → cong from (to∘from y) ≡ from∘to (from y)
    owo y with cong from (to∘from y) | from∘to (from y)
    ... | p | q with trans (cong to p) (sym (to∘from (to (from y)))) | inspect (trans (cong to p)) (sym (to∘from (to (from y))))
    ... | refl | [ eq ] = {!!}

    helper : (y : B) → cong (to ∘ from) (to∘from y) ≡ cong to (from∘to (from y))
    helper y = trans (cong-∘ {f = to} (to∘from y)) (cong (cong to) (owo y))


≃-is-⇔ : (A ≃ B) ≃ (A ⇔ B)
≃-is-⇔ = mkIso
  {!!}
  {!!}
  {!!}
  {!!}

-}



---------------------------------
--         ≃-Reasoning         --
---------------------------------


infix  1 ≃-begin_
infixr 2 _≃⟨_⟩_
infix  3 _≃-∎


≃-begin_ : A ≃ B → A ≃ B 
≃-begin_ = id


_≃⟨_⟩_ : (A : Set a) → A ≃ B → B ≃ C → A ≃ C
_ ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C


_≃-∎ : (A : Set a) → A ≃ A
_ ≃-∎ = ≃-refl



---------------------------------
--        Algebraic Iso        --
---------------------------------


private
  variable
    α : Set a
    β : Set b
    γ : Set c
    δ : Set d


infixl 6 _+_
infixl 7 _*_
infixr 8 _^_


𝟘 = ⊥
𝟙 = ⊤
suc = Maybe
two = suc 𝟙
_+_ = _⊎_
_*_ = _×_

_^_ : Set a → Set b → _
α ^ β = β → α



≃-* : α ≃ β → γ ≃ δ → α * γ ≃ β * δ
≃-* (mkIso α→β β→α α→eq β→eq) (mkIso γ→δ δ→γ γ→eq δ→eq) =
  mkIso
    (λ where
      (a , c) → α→β a , γ→δ c)
    (λ where
      (b , d) → β→α b , δ→γ d)
    (λ where
      (a , c) → cong₂ _,_ (α→eq a) (γ→eq c))
    (λ where
      (b , d) → cong₂ _,_ (β→eq b) (δ→eq d))


≃-+ : α ≃ β → γ ≃ δ → α + γ ≃ β + δ
≃-+ (mkIso α→β β→α α→eq β→eq) (mkIso γ→δ δ→γ γ→eq δ→eq) =
  mkIso
    (λ where
      (inj₁ a) → inj₁ (α→β a)
      (inj₂ c) → inj₂ (γ→δ c))
    (λ where
      (inj₁ b) → inj₁ (β→α b)
      (inj₂ d) → inj₂ (δ→γ d))
    (λ where
      (inj₁ a) → cong inj₁ (α→eq a)
      (inj₂ c) → cong inj₂ (γ→eq c))
    (λ where
      (inj₁ b) → cong inj₁ (β→eq b)
      (inj₂ d) → cong inj₂ (δ→eq d))


≃-suc : α ≃ β → suc α ≃ suc β
≃-suc (mkIso α→β β→α α→eq β→eq) =
  mkIso
    (M.map α→β)
    (M.map β→α)
    (λ where
      nothing  → refl
      (just a) → cong just (α→eq a))
    (λ where
      nothing → refl
      (just b) → cong just (β→eq b))


≃-^ : α ≃ β → γ ≃ δ → γ ^ α ≃ δ ^ β
≃-^ (mkIso α→β β→α α→eq β→eq) (mkIso γ→δ δ→γ γ→eq δ→eq) =
  mkIso
    (λ f → γ→δ ∘ f ∘ β→α)
    (λ g → δ→γ ∘ g ∘ α→β)
    (λ f → fun-ext λ a →
      begin
        f a
      ≡⟨ cong f (α→eq a) ⟩
        f (β→α (α→β a))
      ≡⟨ γ→eq (f (β→α (α→β a))) ⟩
        δ→γ (γ→δ (f (β→α (α→β a))))
      ∎)
    (λ g → fun-ext λ b →
      begin
        g b
      ≡⟨ cong g (β→eq b) ⟩
        g (α→β (β→α b))
      ≡⟨ δ→eq (g (α→β (β→α b))) ⟩
        γ→δ (δ→γ (g (α→β (β→α b))))
      ∎)


+-comm : α + β ≃ β + α
+-comm = mkIso S.swap S.swap
  (λ where
    (inj₁ _) → refl
    (inj₂ _) → refl)
  (λ where
    (inj₁ _) → refl
    (inj₂ _) → refl)


+-assoc : (α + β) + γ ≃ α + (β + γ)
+-assoc = mkIso
  (λ where
    (inj₁ (inj₁ a)) → inj₁ a
    (inj₁ (inj₂ b)) → inj₂ (inj₁ b)
    (inj₂ c) → inj₂ (inj₂ c))
  (λ where
    (inj₁ a) → inj₁ (inj₁ a)
    (inj₂ (inj₁ b)) → inj₁ (inj₂ b)
    (inj₂ (inj₂ c)) → inj₂ c)
  (λ where
    (inj₁ (inj₁ _)) → refl
    (inj₁ (inj₂ _)) → refl
    (inj₂ _) → refl)
  (λ where
    (inj₁ _) → refl
    (inj₂ (inj₁ _)) → refl
    (inj₂ (inj₂ _)) → refl)


*-comm : α * β ≃ β * α
*-comm = mkIso P.swap P.swap
  (λ where
    (_ , _) → refl)
  (λ where
    (_ , _) → refl)


*-assoc : (α * β) * γ ≃ α * (β * γ)
*-assoc = mkIso
  (λ where
    ((a , b) , c) → a , b , c)
  (λ where
    (a , (b , c)) → (a , b) , c)
  (λ where
    ((_ , _) , _) → refl)
  (λ where
    (_ , (_ , _)) → refl)


*-dist : α * (β + γ) ≃ α * β + α * γ
*-dist = mkIso
  (λ where
    (a , inj₁ b) → inj₁ (a , b)
    (a , inj₂ c) → inj₂ (a , c))
  (λ where
    (inj₁ (a , b)) → a , inj₁ b
    (inj₂ (a , c)) → a , inj₂ c)
  (λ where
    (_ , inj₁ _) → refl
    (_ , inj₂ _) → refl)
  (λ where
    (inj₁ (_ , _)) → refl
    (inj₂ (_ , _)) → refl)


≃-curry : (γ ^ β) ^ α ≃ γ ^ (α * β)
≃-curry = mkIso
  uncurry
  curry
  (λ _ → refl)
  (λ _ → fun-ext λ where
    (_ , _) → refl)


≃-1 : 𝟙 ≃ suc 𝟘
≃-1 = mkIso (const nothing) (const tt)
  (λ where
    tt → refl)
  (λ where
    nothing → refl)


+-zero : 𝟘 + β ≃ β
+-zero = mkIso
  (λ where
    (inj₂ b) → b)
  inj₂
  (λ where
    (inj₂ _) → refl)
  (λ _ → refl)


+-suc : suc α + β ≃ suc (α + β)
+-suc = mkIso
  (λ where
    (inj₁ ma) → M.map inj₁ ma
    (inj₂ b) → just (inj₂ b))
  (λ where
    nothing → inj₁ nothing
    (just (inj₁ a)) → inj₁ (just a)
    (just (inj₂ b)) → inj₂ b)
  (λ where
    (inj₁ nothing) → refl
    (inj₁ (just _)) → refl
    (inj₂ _) → refl)
  (λ where
    nothing → refl
    (just (inj₁ _)) → refl
    (just (inj₂ _)) → refl)


1+≃suc : 𝟙 + β ≃ suc β
1+≃suc {β = β} =
  ≃-begin
    𝟙 + β
  ≃⟨ ≃-+ ≃-1 ≃-refl ⟩
    suc 𝟘 + β
  ≃⟨ +-suc ⟩
    suc (𝟘 + β)
  ≃⟨ ≃-suc +-zero ⟩
    suc β
  ≃-∎


*-zero : 𝟘 * β ≃ 𝟘
*-zero = mkIso proj₁ ⊥-elim (⊥-elim ∘ proj₁) λ ()


*-one : 𝟙 * β ≃ β
*-one = mkIso proj₂ (tt ,_)
  (λ where
    (tt , _) → refl)
  (λ _ → refl)


*-suc : suc α * β ≃ β + α * β
*-suc {α = α} {β = β} =
  ≃-begin
    suc α * β
  ≃⟨ ≃-* (≃-sym 1+≃suc) ≃-refl ⟩
    (𝟙 + α) * β
  ≃⟨ *-comm ⟩
    β * (𝟙 + α)
  ≃⟨ *-dist ⟩
    β * 𝟙 + β * α
  ≃⟨ ≃-+ *-comm ≃-refl ⟩
    𝟙 * β + β * α
  ≃⟨ ≃-+ *-one *-comm ⟩
    β + α * β
  ≃-∎


*-two : two * β ≃ β + β
*-two {β = β} =
  ≃-begin
    two * β
  ≃⟨ *-suc ⟩
    β + 𝟙 * β
  ≃⟨ ≃-+ ≃-refl *-one ⟩
    β + β
  ≃-∎


^-zero : α ^ 𝟘 ≃ 𝟙
^-zero = mkIso (λ _ → tt) (λ _ ())
  (λ _ → fun-ext λ ())
  (λ where
    tt → refl)


^-suc : α ^ suc β ≃ α * α ^ β
^-suc = mkIso
  (λ f → f nothing , f ∘ just)
  (λ where
    (a , _) nothing → a
    (_ , f) (just b) → f b)
  (λ f → fun-ext λ where
    nothing → refl
    (just _) → refl)
  (λ where
    (_ , _) → refl)


^-one : α ^ 𝟙 ≃ α
^-one {α = α} =
  ≃-begin
    α ^ 𝟙
  ≃⟨ ≃-^ ≃-1 ≃-refl ⟩
    α ^ suc 𝟘
  ≃⟨ ^-suc ⟩
    α * α ^ 𝟘
  ≃⟨ ≃-* ≃-refl ^-zero ⟩
    α * 𝟙
  ≃⟨ *-comm ⟩
    𝟙 * α
  ≃⟨ *-one ⟩
    α
  ≃-∎


^-two : α ^ two ≃ α * α
^-two {α = α} =
  ≃-begin
    α ^ two
  ≃⟨ ^-suc ⟩
    α * α ^ 𝟙
  ≃⟨ ≃-* ≃-refl ^-one ⟩
    α * α
  ≃-∎


+-square : (α + β) ^ two ≃ α ^ two + two * α * β + β ^ two
+-square {α = α} {β = β} =
  ≃-begin
    (α + β) ^ two
  ≃⟨ ^-suc ⟩
    (α + β) * (α + β) ^ 𝟙
  ≃⟨ ≃-* ≃-refl ^-one ⟩
    (α + β) * (α + β)
  ≃⟨ *-dist ⟩
    (α + β) * α + (α + β) * β
  ≃⟨ ≃-+ *-comm *-comm ⟩
    α * (α + β) + β * (α + β)
  ≃⟨ ≃-+ *-dist *-dist ⟩
    α * α + α * β + (β * α + β * β)
  ≃⟨ ≃-+ (≃-+ (≃-sym ^-two) ≃-refl) (≃-+ *-comm (≃-sym ^-two)) ⟩
    α ^ two + α * β + (α * β + β ^ two)
  ≃⟨ +-assoc ⟩
    α ^ two + (α * β + (α * β + β ^ two))
  ≃⟨ ≃-+ ≃-refl (≃-sym +-assoc) ⟩
    α ^ two + (α * β + α * β + β ^ two)
  ≃⟨ ≃-+ ≃-refl (≃-+ (≃-sym *-two) ≃-refl) ⟩
    α ^ two + (two * (α * β) + β ^ two)
  ≃⟨ ≃-+ ≃-refl (≃-+ (≃-sym *-assoc) ≃-refl) ⟩
    α ^ two + (two * α * β + β ^ two)
  ≃⟨ ≃-sym +-assoc ⟩
    α ^ two + two * α * β + β ^ two
  ≃-∎
