module vector where

open import base
open import nat
open import prop
open import eq
open import func



---------------------------------
--         Definitions         --
---------------------------------


infixr 5 _∷_
infixl 5 _++_


data Vec (A : Set a) : ℕ → Set a where
  [] : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)


_++_ : ∀ {m n} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


map : ∀ {n} → (A → B) → Vec A n → Vec B n
map _ [] = []
map f (x ∷ xs) = f x ∷ map f xs


zipWith : ∀ {n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith _ [] [] = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys


replicate : ∀ n → A → Vec A n
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x



---------------------------------
--         Properties          --
---------------------------------


map0*-replicate : ∀ {n} (xs : Vec ℕ n) → map (0 *_) xs ≡ replicate n 0
map0*-replicate [] = refl
map0*-replicate (_ ∷ xs) = cong (0 ∷_) (map0*-replicate xs)


map1* : ∀ {n} (xs : Vec ℕ n) → map (1 *_) xs ≡ xs
map1* [] = refl
map1* (x ∷ xs)
    rewrite +-identityʳ x
  = cong (x ∷_) (map1* xs)


zipWith-assoc : ∀ {n} (f : A → A → A)
              → Assoc A f
              → Assoc (Vec A n) (zipWith f)
zipWith-assoc _ _ [] [] [] = refl
zipWith-assoc f f-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs)
    rewrite f-assoc x y z
  = cong (f x (f y z) ∷_) (zipWith-assoc f f-assoc xs ys zs)


zipWith-comm : ∀ {n} (f : A → A → A)
             → Comm A f
             → Comm (Vec A n) (zipWith f)
zipWith-comm _ _ [] [] = refl
zipWith-comm f f-comm (x ∷ xs) (y ∷ ys)
    rewrite f-comm x y
  = cong (f y x ∷_) (zipWith-comm f f-comm xs ys)


zipWith-+-zero : ∀ {n} ys → zipWith _+_ (replicate n 0) ys ≡ ys
zipWith-+-zero [] = refl
zipWith-+-zero (y ∷ ys) = cong (y ∷_) (zipWith-+-zero ys)


zipWith-map-+-* : ∀ {n} k p (xs : Vec ℕ n) → map ((k + p) *_) xs ≡ zipWith _+_ (map (k *_) xs) (map (p *_) xs)
zipWith-map-+-* _ _ [] = refl
zipWith-map-+-* k p (x ∷ xs)
    rewrite *-distribʳ-+ x k p
  = cong (k * x + p * x ∷_) (zipWith-map-+-* k p xs)


∘-map : ∀ {n} (f : B → C) (g : A → B) (xs : Vec A n) → map (f ∘ g) xs ≡ map f (map g xs)
∘-map _ _ [] = refl
∘-map f g (x ∷ xs) = cong (f (g x) ∷_) (∘-map f g xs)
