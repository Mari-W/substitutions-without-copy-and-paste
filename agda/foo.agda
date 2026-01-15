{-# OPTIONS --rewriting --local-confluence-check #-}
module foo where 

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
  h′ i′ j′ k′ o′ : ℕ
  h′′ i′′ j′′ k′′ o′′ : ℕ
  -- M N : Matrix
  q r s : ℕ
  q′ r′ s′ : ℕ
  q′′ r′′ s′′ : ℕ

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
data Mode : Matrix → Set where
  ex : (q : ℕ) → Mode (q , 1 , 1 , 0) 
  ty : (q : ℕ) → Mode (q , 1 , 0 , 1)
  su : (q : ℕ) → Mode (q , 0 , 1 , 0)
  cx : Mode (2 , 0 , 0 , 0) 
  ki : Mode (2 , 0 , 0 , 1) 

⟦_⟧ : 

variable
  m n   : Mode (q , i , j , o) 

{- ⟦_⟧′ : Mode (q , i , j , o) → Structure Mode
⟦ ex q ⟧′ = {!   !}
⟦ ty q ⟧′ = {!   !}
⟦ su q ⟧′ = {!   !}
⟦ cx ⟧′ = ■
⟦ ki ⟧′ = ■ -}

⟦_⟧′ : Mode (q , i , j , o) → Set
data Tm : (m : Mode (q , i , j  , o)) → ⟦ m ⟧′ → Set   

⟦ m ⟧′ = {!   !}
