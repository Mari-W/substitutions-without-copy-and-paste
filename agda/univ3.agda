{-# OPTIONS --rewriting --local-confluence-check --sized-types #-}
module univ3 where 

open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning public
open import Data.List using (List; _∷_; [])
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; -,_; ∃; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _∸_)
{-# BUILTIN REWRITE _≡_ #-}
open import Size

SSet = ℕ → Set
SSet₁ = ℕ → Set₁

variable
  n m : ℕ 

data Desc↑ (I : SSet) : SSet₁ where
  ′∃  : ∀ {n} → I (suc n) → Desc↑ I (suc n) → Desc↑ I (suc n)
  ′↑_ : ∀ {n} → Desc↑ I n → Desc↑ I (suc n)
  ′■  : ∀ {n} → Desc↑ I n

SDesc↑ : (ℕ → Set) → Set₁
SDesc↑ I = ∀ {n} → I (suc n) → Desc↑ I n


record SITU : Set₁ where
  field
    Sort : SSet
    D↑   : SDesc↑ Sort
    hierachy : Sort (suc n) → List (Sort n)

  data Desc : Set
  
  module _ (d : Desc) where
    ⟦_⟧ : D↑ → Set 
    data Tm : (s : Sort (suc n)) → ⟦ s ⟧ → Set 
      
    ⟦ s    ⟧ = {!   !}