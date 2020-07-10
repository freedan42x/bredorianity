module vector where

open import base
open import nat
open import prop
open import eq



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


foldr : ∀ {n} → (A → B → B) → B → Vec A n → B
foldr f d [] = d
foldr f d (x ∷ xs) = f x (foldr f d xs)


zipWith : ∀ {n} → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith _ [] [] = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys


replicate : ∀ n → A → Vec A n
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x



---------------------------------
--         Properties          --
---------------------------------


zipWith-assoc : ∀ {n} (f : A → A → A)
              → Assoc A f
              → Assoc (Vec A n) (zipWith f)
zipWith-assoc _ _ [] [] [] = refl
zipWith-assoc f f-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs)
    rewrite sym (f-assoc x y z)
  = cong (f (f x y) z ∷_) (zipWith-assoc f f-assoc xs ys zs)


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
