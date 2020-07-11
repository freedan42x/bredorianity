module iso where

open import base
open import eq
open import func
open import prop
open import prod



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
    ... | refl | [ eq ] = trans {!!} {!!}

    helper : (y : B) → cong (to ∘ from) (to∘from y) ≡ cong to (from∘to (from y))
    helper y = trans (cong-∘ {f = to} (to∘from y)) (cong (cong to) (owo y))


-- cong (to ∘ from) (to∘from y) ≡ cong to (from∘to (from y))

{-
≃-is-⇔ : (A ≃ B) ≃ (A ⇔ B)
≃-is-⇔ = mkIso
  {!!}
  {!!}
  {!!}
  {!!}
-}
