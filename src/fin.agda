module fin where

open import nat
open import Data.Fin using (Fin; toℕ; fromℕ; raise) renaming (zero to fzero; suc to fsuc) public



asF : (n l : ℕ) → Fin (suc l)
asF zero l = fzero
asF (suc n) zero = asF n zero
asF (suc n) (suc l) = fsuc (asF n l)
