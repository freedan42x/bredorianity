module matrix where

open import nat
open import vector
open import eq
open import prop
open import fin


private
  variable
    m n p : ℕ



---------------------------------
--         Definitions         --
---------------------------------


infixl 6 _M+_
infix 7 _S*_
infixl 7 _M*_


Matrix : ℕ → ℕ → Set
Matrix m n = Vec (Vec ℕ n) m


Z : ∀ m n → Matrix m n
Z m n = replicate m (replicate n 0)


_M+_ : Matrix m n → Matrix m n → Matrix m n
[] M+ [] = []
(r1 ∷ A) M+ (r2 ∷ B) = zipWith _+_ r1 r2 ∷ (A M+ B)


_S*_ : ℕ → Matrix m n → Matrix m n
k S* xs = map (map (k *_)) xs


_ᵀ : Matrix (suc m) n → Matrix n (suc m)
([] ∷ _) ᵀ = []
_ᵀ {n = suc n} xs = map head xs ∷ (map tail xs) ᵀ


_M*_ : Matrix m (suc n) → Matrix (suc n) p → Matrix m p
_M*_ A B = map (λ r → map (λ c → sum (zipWith _*_ r c)) (B ᵀ)) A


Sq : ℕ → Set
Sq n = Matrix n n


I : ∀ n → Sq n
I zero = []
I n@(suc l) = map (λ k → set (asF k l) 1 (replicate n 0)) (count n)



---------------------------------
--         Properties          --
---------------------------------


M+-Zˡ : (A : Matrix m n) → Z m n M+ A ≡ A
M+-Zˡ [] = refl
M+-Zˡ (r ∷ A)
    rewrite zipWith-+-zero r
  = cong (r ∷_) (M+-Zˡ A)


M+-Zʳ : (A : Matrix m n) → A M+ Z m n ≡ A
M+-Zʳ [] = refl
M+-Zʳ {n = n} (r ∷ A)
    rewrite zipWith-comm _+_ +-comm r (replicate n 0)
  | zipWith-+-zero r
  = cong (r ∷_) (M+-Zʳ A)


M+-assoc : Assoc (Matrix m n) _M+_
M+-assoc [] [] [] = refl
M+-assoc (r1 ∷ A) (r2 ∷ B) (r3 ∷ C)
    rewrite zipWith-assoc _+_ +-assoc r1 r2 r3
  = cong (zipWith _+_ r1 (zipWith _+_ r2 r3) ∷_) (M+-assoc A B C)


M+-comm : (A B : Matrix m n) → A M+ B ≡ B M+ A
M+-comm [] [] = refl
M+-comm (r1 ∷ A) (r2 ∷ B)
    rewrite zipWith-comm _+_ +-comm r1 r2
  | fun-ext (λ y → fun-ext λ x → +-comm x y)
  = cong (zipWith _+_ r2 r1 ∷_) (M+-comm A B)


S*-zero : (A : Matrix m n) → 0 S* A ≡ Z m n
S*-zero [] = refl
S*-zero {n = n} (r ∷ A)
    rewrite map0*-replicate r
  = cong (replicate n 0 ∷_) (S*-zero A)


S*-one : (A : Matrix m n) → 1 S* A ≡ A
S*-one [] = refl
S*-one (r ∷ A)
    rewrite map1* r
  = cong (r ∷_) (S*-one A)


S*-distrib : ∀ k p (A : Matrix m n) → (k + p) S* A ≡ k S* A M+ p S* A
S*-distrib _ _ [] = refl
S*-distrib k p (r ∷ A)
    rewrite zipWith-map-+-* k p r
  = cong (zipWith _+_ (map (k *_) r) (map (p *_) r) ∷_) (S*-distrib k p A)


S*-assoc : ∀ k p (A : Matrix m n) → (k * p) S* A ≡ k S* (p S* A)
S*-assoc _ _ [] = refl
S*-assoc k p (r ∷ A)
    rewrite fun-ext (λ x → *-assoc k p x)
  | ∘-map (k *_) (p *_) r
  | fun-ext (λ x → sym (*-assoc k p x))
  = cong (map (k *_) (map (p *_) r) ∷_) (S*-assoc k p A)


M*-idˡ : ∀ n (A : Sq (suc n)) → I (suc n) M* A ≡ A
M*-idˡ n ((x ∷ r) ∷ A)
    rewrite +-identityʳ x
  | zipWith-*-zero (map head A)
  | sum-replicate-0 n
  | +-identityʳ x
  = begin
      (x ∷
         map (λ c → sum (zipWith _*_ (1 ∷ replicate n 0) c))
         ((r ∷ map tail A) ᵀ))
        ∷
        map
        (λ r₁ →
           sum (zipWith _*_ r₁ (x ∷ map head A)) ∷
           map (λ c → sum (zipWith _*_ r₁ c)) ((r ∷ map tail A) ᵀ))
        (map (λ k → set (asF k n) 1 (0 ∷ replicate n 0)) (count-acc 1 n))
    ≡⟨ {!!} ⟩
      (x ∷ r) ∷ A
    ∎
