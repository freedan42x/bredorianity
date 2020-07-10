module matrix where

open import nat
open import vector
open import eq
open import prop



---------------------------------
--         Definitions         --
---------------------------------


Matrix : ℕ → ℕ → Set
Matrix m n = Vec (Vec ℕ n) m

MatrixZ : ∀ m n → Matrix m n
MatrixZ m n = replicate m (replicate n 0)

infixl 6 _M+_
_M+_ : ∀ {m n} → Matrix m n → Matrix m n → Matrix m n
[] M+ [] = []
(r1 ∷ A) M+ (r2 ∷ B) = zipWith _+_ r1 r2 ∷ (A M+ B)



---------------------------------
--         Properties          --
---------------------------------


M+-zeroˡ : ∀ {m n} (A : Matrix m n) → MatrixZ m n M+ A ≡ A
M+-zeroˡ [] = refl
M+-zeroˡ (r ∷ A)
    rewrite zipWith-+-zero r
  = cong (r ∷_) (M+-zeroˡ A)

M+-zeroʳ : ∀ {m n} (A : Matrix m n) → A M+ MatrixZ m n ≡ A
M+-zeroʳ [] = refl
M+-zeroʳ {n = n} (r ∷ A)
    rewrite zipWith-comm _+_ +-comm r (replicate n 0)
  | zipWith-+-zero r
  = cong (r ∷_) (M+-zeroʳ A)

M+-assoc : ∀ {m n} → Assoc (Matrix m n) _M+_
M+-assoc [] [] [] = refl
M+-assoc (r1 ∷ A) (r2 ∷ B) (r3 ∷ C) rewrite
    zipWith-assoc _+_ +-assoc r1 r2 r3
  = cong (zipWith _+_ r1 (zipWith _+_ r2 r3) ∷_) (M+-assoc A B C)

M+-comm : ∀ {m n} (A B : Matrix m n) → A M+ B ≡ B M+ A
M+-comm [] [] = refl
M+-comm (r1 ∷ A) (r2 ∷ B)
    rewrite  zipWith-comm _+_ +-comm r1 r2
  | fun-ext (λ y → fun-ext λ x → +-comm x y)
  = cong (zipWith _+_ r2 r1 ∷_) (M+-comm A B)
