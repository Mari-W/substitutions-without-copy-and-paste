{-# OPTIONS --rewriting --local-confluence-check --sized-types #-}
module univ2 where 

open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning public
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; -,_; ∃; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _∸_)
{-# BUILTIN REWRITE _≡_ #-}
open import Size

ISet = ℕ → Set
ISet₁ = ℕ → Set₁

data Desc↑ (I : ISet) : ISet₁ where
  ′∃ : ∀ {n} → I (suc n) → Desc↑ I (suc n) → Desc↑ I (suc n)
  ′↓_ : ∀ {n} → Desc↑ I n → Desc↑ I (suc n)
  ′■ : ∀ {n} → Desc↑ I n

IDesc↑ : (ℕ → Set) → Set₁
IDesc↑ I = ∀ {n} → I (suc n) → Desc↑ I n

module ISyn {I : ISet} (D↑ : IDesc↑ I) where
  data ⊤₁ : Set₁ where 
    tt₁ : ⊤₁

  ⟦_⟧′ : ∀ {n} → Desc↑ I n → Set₁

  ⟦_⟧′′ : ∀ {n} → I (suc n) → Set₁
  ⟦ i ⟧′′ = ⟦ D↑ i ⟧′ 

  Scope : Set₁ 
  Scope = {!   !} 

  data Desc : {n : ℕ} (i : I (suc n)) → ⟦ i ⟧′′ → Set₁ where
    ′σ : ∀ {n} {i : I (suc n)} {⟦i⟧ : ⟦ i ⟧′′} →

      (A : Set₁) → 
      (A → Σ[ j ∈ I (suc n) ] Σ[ ⟦j⟧ ∈ ⟦ j ⟧′′ ] 
      Desc j ⟦j⟧) → 
      ------------------------------------------
      Desc i ⟦i⟧

    ′X : {!   !}

    ′■ : ∀ {m} {i : I (suc m)} (⟦i⟧ : ⟦ i ⟧′′) → 
      
      ----------
      Desc i ⟦i⟧  

  ⟦ ′∃ i d ⟧′ = ∃[ ⟦d⟧′ ] Desc i ⟦d⟧′ × (⟦ d ⟧′)
  ⟦ ′↓ d   ⟧′ = ⟦ d ⟧′
  ⟦ ′■     ⟧′ = ⊤₁

  _-Scoped : ∀ {n} (i : I (suc n)) → Set₂

  ⟦_⟧ : ∀ {n m} {i : I (suc n)} {j : I (suc m)} {⟦i⟧ : ⟦ i ⟧′′} → 
    Desc i ⟦i⟧ → (Scope → j -Scoped) → i -Scoped

  i -Scoped = (S : Scope) → {! ⟦ ? ⟧   !} → Set₁  

 
  ⟦ ′σ A d ⟧ X Γ ⟦i⟧ = Σ[ a ∈ A ] 
    let j , ⟦j⟧ , d = d a in
    (⟦ d ⟧ X ⟦j⟧ Γ)
  ⟦ ′■ ⟦j⟧ ⟧ X Γ ⟦i⟧ = ⟦j⟧ ≡ ⟦i⟧ 

  data Tm {n : ℕ} {i : I (suc n)} {⟦i⟧ : ⟦ i ⟧′′} (d : Desc i ⟦i⟧) : 
    Size → i -Scoped → Set₁ where
    

data Sort : ISet where
--   un : ∀ {n} → Sort n
  ↓_ : ∀ {n} → Sort (suc n) → Sort (suc (suc n))

  ex : Sort 2
  ty : Sort 1

D↑ : IDesc↑ Sort
-- D↑ un = ′■ 
D↑ (↓ s) = ′↓ (D↑ s)
D↑ ex = ′∃ ty ′■
D↑ ty = ′■
open ISyn D↑ 

data Label : Set₁ where 
  ⟦⊤⟧ : Label 
  ⟦⇒⟧ : {!   !} →  Label
  ⟦λ⟧ ⟦∙⟧ : Label

desc : ∀ {n} → (s : Sort (suc n)) → Desc s {!   !}
desc s = ′σ Label λ where
  x → {!   !}
  -- ⟦⊤⟧ → (↓ ↓ ty) , tt₁ , ′■ tt₁
  -- ⟦⇒⟧ → (↓ ↓ ty) , tt₁ , {!   !}
  -- ⟦λ⟧ → {!   !}
  -- ⟦∙⟧ → {!   !}

{- data Sort : ISet where
  ↓_ : ∀{n} → Sort (suc n) → Sort (suc (suc n))
  ex : Sort 3
  ty : Sort 2
  cx : Sort 1
  ki : Sort 1
  un : Sort 1

D↑ : IDesc↑ Sort
D↑ ex = ′∃ (↓ cx) (′∃ ty ′■)
D↑ ty = ′∃ cx (′∃ ki ′■)
D↑ ki = ′■
D↑ cx = ′■
D↑ un = ′■
D↑ (↓ s) = ′↓ (D↑ s)

open ISyn D↑ 

open import Data.Bool

data Label : Set where 


_ : Desc un tt₁
_ = ′σ Bool λ where
  false → cx , (tt₁ , ′■ tt₁)
  true → {!   !} -}

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
  -- ⟦_⟧′↑ : Desc↑ ? → ? 
  -- data Desc↑ : Set where