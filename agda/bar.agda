{-# OPTIONS --rewriting --local-confluence-check #-}
module bar where 

open import Relation.Binary.PropositionalEquality hiding ([_]; J)
open ≡-Reasoning public
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; -,_; ∃; Σ-syntax; ∃-syntax; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _∸_)
{-# BUILTIN REWRITE _≡_ #-}

infix   3  _⊢[_]_
infix   3  _⊩[_]_
infixl  4  _,_
infix   5  _∘_
infix   5  ƛ_
infixl  6  _·_
infix   7  `_
infix   8  _⁺_
infix   8  _↑_
infix   8  _[_]

Matrix = ℕ × ℕ × ℕ × ℕ 

variable
  h i j k o : ℕ

  -- M N : Matrix
  q r s : ℕ


MODE = Matrix → Set


variable 
  M : MODE

-- data Structure (M : MODE) : Set
-- _⟦⟦_⟧⟧ : Structure M → Set
-- 
-- data Structure M where
--   
--   ■ : Structure M
-- 
-- ⟦⟦ ■ ⟧⟧ = {!   !}

-- VarTm / Bind / Termination / Ctx
{- data Mode :  Set where
  ex : Mode 
  ty : Mode 
  ki : Mode
  su : Mode
  cx : Mode -}
  
data Mode : Set where
  ex : Mode
  ty : Mode
  ki : Mode
  su : Mode
  cx : Mode

data Desc (I J : Set) : Set1 where
  ‘σ : (A : Set) → (A → Desc I J) → Desc I J
  ‘X : J → Desc I J → Desc I J
  ‘■ : I → Desc I J

variable 
  I J : Set

⟦_⟧ : Desc I J → (J → Set) → (I → Set)
⟦ ‘σ A d ⟧ X i = Σ[ a ∈ A ] (⟦ d a ⟧ X i)
⟦ ‘X j d ⟧ X i = X j × ⟦ d ⟧ X i
⟦ ‘■ i′ ⟧ X i = i ≡ i′

listD : Set → Desc ⊤ ⊤
listD A = ‘σ Mode {!   !}

{- ⟦_⟧ᵀ : 
    {A : ∀ {q} → Mode q → Set} 
    {Tm : ∀ {q} (m : Mode q) → (A m) → Set} → 
   Mode q → Set 
⟦_⟧ᵀ {Tm = Tm} ex = ∃[ T ] Tm ty T
⟦_⟧ᵀ {Tm = Tm} ty = ∃[ Γ ] ∃[ * ] Σ[ _ ∈ Tm cx Γ ] Tm ki *
⟦_⟧ᵀ {Tm = Tm} ki = ⊤
⟦_⟧ᵀ {Tm = Tm} su = ∃[ Γ ] ∃[ Δ ] Σ[ _ ∈ Tm cx Γ ] Tm cx Δ
⟦_⟧ᵀ {Tm = Tm} cx = ⊤  -}


⟦_⟧′ : Mode → Set
data Tm : (m : Mode) → ⟦ m ⟧′ → Set   
⟦_⟧′ m = {!   !}  

-- ⟦_⟧ ex = ∃[ T ] Tm ty T
-- ⟦_⟧ ty = ∃[ Γ ] ∃[ * ] Σ[ _ ∈ Tm cx Γ ] Tm ki *
-- ⟦_⟧ ki = ⊤
-- ⟦_⟧ su = ∃[ Γ ] ∃[ Δ ] Σ[ _ ∈ Tm cx Γ ] Tm cx Δ
-- ⟦_⟧ cx = ⊤ 
