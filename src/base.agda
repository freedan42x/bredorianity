module base where

open import Level using (Level; 0ℓ) renaming (suc to ℓsuc; _⊔_ to ℓmax) public


variable
  a b c d e : Level
  A : Set a
  B : Set b
  C : Set c
  D : Set d
  E : Set e
