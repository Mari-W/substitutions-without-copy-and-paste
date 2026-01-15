{-# OPTIONS --rewriting --local-confluence-check --sized-types #-}
module univ where 

open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning public
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; -,_; ∃; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _∸_)
{-# BUILTIN REWRITE _≡_ #-}
open import Size

data Desc↑ (I : ℕ → Set) : ℕ → Set₁ where
  ′∃ : ∀ {n} → I (suc n) → Desc↑ I (suc n) → Desc↑ I (suc n)
  ′↓_ : ∀ {n} → Desc↑ I n → Desc↑ I (suc n)
  ′■ : ∀ {n} → Desc↑ I n

variable
  I : ℕ → Set

{- data Sort : Size → Set where 
  ex : ∀ {e} → Sort e   
  ty : ∀ {t} → Sort (t ⊔ˢ {! sort ex  !})

data Mode : Set where 
  ex ty ki cx : Mode 

D↑′ : {j : Size} → Mode → Desc↑ Mode j 
D↑′ ex = {!   !}
D↑′ ty = {!   !} -- ′∃ cx (D↑′ ki)
D↑′ ki = ′■
D↑′ cx = ′■ -}

data Sort : ℕ → Set where
  ↓_ : ∀{n} → Sort (suc n) → Sort (suc (suc n))
  ex : Sort 3
  ty : Sort 2
  cx : Sort 1
  ki : Sort 1

D↑ : ∀ {n} → Sort (suc n) → Desc↑ Sort n
D↑ ex = ′∃ (↓ cx) (′∃ ty ′■)
D↑ ty = ′∃ cx (′∃ ki ′■)
D↑ ki = ′■
D↑ cx = ′■
D↑ (↓ s) = ′↓ (D↑ s)

data ⊤₁ : Set₁ where 
  tt₁ : ⊤₁
 
_⟦_⟧ : ∀{n} → (∀ {n} → I (suc n) → Desc↑ I n) → Desc↑ I n → Set₁
data Desc 
  {I : ℕ → Set} {n : ℕ} (D↑ : ∀ {n} → I (suc n) → Desc↑ I n) : 
  (i : I (suc n)) → D↑ ⟦ D↑ i ⟧ → Set₁ where
   
D↑ ⟦ ′∃ i d ⟧ = ∃[ ⟦d⟧ ] Desc D↑ i ⟦d⟧ × (D↑ ⟦ d ⟧)
D↑ ⟦ ′↓ d   ⟧ = D↑ ⟦ d ⟧
D↑ ⟦ ′■     ⟧ = ⊤₁

_ = {! D↑ ⟦ D↑ ex ⟧ !}   
{- 
data STLC : Set where
  ex ty : STLC  

S : Desc↑ STLC
S = ′σ STLC λ where 
  ex → ′■ ty
  ty → ′⊤


data SystemF : Set where 
  ex ty ki cx : SystemF

S′ : Desc↑ SystemF 
S′ = ′σ SystemF λ where
  ex → {!   !}
  ty → {!   !} -}
-- ⟦_⟧↑ : Desc↑ ? → ? 
-- data Desc↑ : Set where