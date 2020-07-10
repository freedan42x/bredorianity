module base where

open import Level using (Level; 0ℓ) renaming (suc to ℓsuc; _⊔_ to ℓmax) public


variable
  a b c d : Level
  A : Set a
  B : Set b
  C : Set c
  D : Set d
