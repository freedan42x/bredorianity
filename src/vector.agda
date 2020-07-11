module vector where

open import base
open import nat
open import prop
open import eq
open import func
open import fin


private
  variable
    m n : ℕ



---------------------------------
--         Definitions         --
---------------------------------


infixr 5 _∷_
infixl 5 _++_


data Vec (A : Set a) : ℕ → Set a where
  [] : Vec A 0
  _∷_ : A → Vec A n → Vec A (suc n)


head : Vec A (suc n) → A
head (x ∷ _) = x


tail : Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs


_++_ : Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


map : (A → B) → Vec A n → Vec B n
map _ [] = []
map f (x ∷ xs) = f x ∷ map f xs


sum : Vec ℕ n → ℕ
sum [] = 0
sum (x ∷ xs) = x + sum xs


count-acc : ℕ → ∀ n → Vec ℕ n
count-acc k zero = []
count-acc k (suc n) = k ∷ count-acc (suc k) n


count : ∀ n → Vec ℕ n
count n = count-acc 0 n


take : (k : Fin n) → Vec A n → Vec A (toℕ k)
take fzero _ = []
take (fsuc k) (x ∷ xs) = x ∷ take k xs


_!_ : Vec A n → Fin n → A
(x ∷ _) ! fzero = x
(_ ∷ xs) ! fsuc k = xs ! k


set : Fin n → A → Vec A n → Vec A n
set fzero y (_ ∷ xs) = y ∷ xs
set (fsuc k) y (x ∷ xs) = x ∷ set k y xs


zipWith : (A → B → C) → Vec A n → Vec B n → Vec C n
zipWith _ [] [] = []
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys


replicate : ∀ n → A → Vec A n
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x



---------------------------------
--         Properties          --
---------------------------------


map0*-replicate : (xs : Vec ℕ n) → map (0 *_) xs ≡ replicate n 0
map0*-replicate [] = refl
map0*-replicate (_ ∷ xs) = cong (0 ∷_) (map0*-replicate xs)


map1* : (xs : Vec ℕ n) → map (1 *_) xs ≡ xs
map1* [] = refl
map1* (x ∷ xs)
    rewrite +-identityʳ x
  = cong (x ∷_) (map1* xs)


zipWith-assoc : (f : A → A → A)
              → Assoc A f
              → Assoc (Vec A n) (zipWith f)
zipWith-assoc _ _ [] [] [] = refl
zipWith-assoc f f-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs)
    rewrite f-assoc x y z
  = cong (f x (f y z) ∷_) (zipWith-assoc f f-assoc xs ys zs)


zipWith-comm : (f : A → A → A)
             → Comm A f
             → Comm (Vec A n) (zipWith f)
zipWith-comm _ _ [] [] = refl
zipWith-comm f f-comm (x ∷ xs) (y ∷ ys)
    rewrite f-comm x y
  = cong (f y x ∷_) (zipWith-comm f f-comm xs ys)


zipWith-+-zero : ∀ ys → zipWith _+_ (replicate n 0) ys ≡ ys
zipWith-+-zero [] = refl
zipWith-+-zero (y ∷ ys) = cong (y ∷_) (zipWith-+-zero ys)


zipWith-*-zero : ∀ ys → zipWith _*_ (replicate n 0) ys ≡ replicate n 0
zipWith-*-zero [] = refl
zipWith-*-zero (_ ∷ ys) = cong (0 ∷_) (zipWith-*-zero ys)


zipWith-map-+-* : ∀ k p (xs : Vec ℕ n)
                → map ((k + p) *_) xs
                ≡ zipWith _+_ (map (k *_) xs) (map (p *_) xs)
zipWith-map-+-* _ _ [] = refl
zipWith-map-+-* k p (x ∷ xs)
    rewrite *-distribʳ-+ x k p
  = cong (k * x + p * x ∷_) (zipWith-map-+-* k p xs)


∘-map : (f : B → C) (g : A → B) (xs : Vec A n)
      → map (f ∘ g) xs ≡ map f (map g xs)
∘-map _ _ [] = refl
∘-map f g (x ∷ xs) = cong (f (g x) ∷_) (∘-map f g xs)


sum-replicate-0 : ∀ n → sum (replicate n 0) ≡ 0
sum-replicate-0 zero = refl
sum-replicate-0 (suc n) = sum-replicate-0 n
