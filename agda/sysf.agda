{-# OPTIONS --rewriting --local-confluence-check #-}
module sysf where 

open import Relation.Binary.PropositionalEquality hiding ([_])
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

-- VarTm / Bind / Termination / Ctx
data Mode : Matrix → Set where
  ex : (q : ℕ) → Mode (q , 1 , 1 , 0) 
  ty : (q : ℕ) → Mode (q , 1 , 0 , 1)
  su : (q : ℕ) → Mode (q , 0 , 1 , 0)
  cx : Mode (2 , 0 , 0 , 0) 
  ki : Mode (2 , 0 , 0 , 1) 

variable
  h i j k o : ℕ
  h′ i′ j′ k′ o′ : ℕ
  h′′ i′′ j′′ k′′ o′′ : ℕ
  M N : Matrix
  q r s : ℕ
  q′ r′ s′ : ℕ
  q′′ r′′ s′′ : ℕ
  m n   : Mode (q , i , j , o) 

⟦_⟧ : Mode (q , i , j  , o) → Set
data Tm : (m : Mode (q , i , j  , o)) → ⟦ m ⟧ → Set   

⟦ ki   ⟧ = ⊤ 
⟦ cx   ⟧ = ⊤
⟦ su _ ⟧ = Tm cx tt × Tm cx tt
⟦ ex _ ⟧ = ∃[ Γ ] Tm (ty 1) Γ
⟦ ty _ ⟧ = Tm cx tt × Tm ki tt

matrix : Mode M → Matrix
matrix {M} m = M

_↑ᴵ : (m : Mode (q , i , j  , o)) → Matrix
ex _ ↑ᴵ = matrix (ty 1)
ty _ ↑ᴵ = matrix ki
su _ ↑ᴵ = matrix ki
cx ↑ᴵ   = matrix ki
_↑ᴵ {q} {i} {j} {o} ki = q , i , j  , o

_↑ᵀ : (m : Mode (q , i , j  , o)) → Mode (m ↑ᴵ)
cx   ↑ᵀ = ki
su _ ↑ᵀ = ki
ki   ↑ᵀ = ki 
ty _ ↑ᵀ = ki 
ex _ ↑ᵀ = ty 1

⌊_⌋ᵀ : ⟦ m ⟧ → ⟦ m ↑ᵀ ⟧ 
⌊_⌋ᵀ {m = cx}   _       = tt
⌊_⌋ᵀ {m = su _} _       = tt
⌊_⌋ᵀ {m = ki}   _       = tt
⌊_⌋ᵀ {m = ex _} (Γ , _) = Γ
⌊_⌋ᵀ {m = ty _} _       = tt

⌊_∣_⌋ᵀ : {m : Mode (q , i , j , o)} (n : Mode (q′ , i′ , j′ , 1)) →
  ⟦ m ⟧ → ⟦ n ⟧  
⌊_∣_⌋ᵀ ki _     = tt
⌊_∣_⌋ᵀ {m = ex q} (ty _) (⟦m⟧ , _) = ⟦m⟧
⌊_∣_⌋ᵀ {m = ty q} (ty _) ⟦m⟧ = ⟦m⟧

_⟦▷⟧_ : ∀ {m : Mode (q , i , j , o)} {n : Mode (q′ , i′ , j′ , 1)} →
  (Q : ⟦ m ⟧) → Tm n ⌊ n ∣ Q ⌋ᵀ → ⟦ m ⟧

_∶_ : ∀ {m : Mode (q , 1 , j  , o)} {n : Mode (q′ , i′ , j′ , 1)} →
  (Q : ⟦ m ⟧) → Tm n ⌊ n ∣ Q ⌋ᵀ → ⟦ m ⟧ 

wk : ∀  {m : Mode (q , i , j , o)} {n : Mode (q′ , i′ , j′ , 1)} {Q} → 
  Tm m Q → (T : Tm n ⌊ n ∣ Q ⌋ᵀ) → Tm m (Q ⟦▷⟧ T)

data Tm where

  *   : ∀ {Q} → 
    ---------- 
    Tm ki Q

  •   : ∀ {Q} → 
    -------------
    Tm cx Q
  _▷_ : ∀ {m : Mode (q , i , j  , 1)} {Q R} →
    Tm cx Q →
    Tm m R → 
    --------------
    Tm cx Q

  ε : ∀ {Q} {Γ : Tm cx Q} →
    ------------------------
    Tm (su q) (Γ ,  •)
  _⸴_ : 
    ∀ {Q R} {Γ : Tm cx Q} {Δ : Tm cx R} {m : Mode (q , i , j  , 1)} {Q} →
    Tm (su q) (Γ ,  Δ) →
    (T : Tm m Q) → 
    Tm (su q) (Γ ,  Δ ▷ T)

  ** : ∀{Γ} → Tm (ty 1) (Γ , *)

  zero  : ∀ {m : Mode (0 , 1 , j  , o)} {n : Mode (q′ , i′ , j′ , 1)} 
    {Q : ⟦ m ⟧} {T : Tm n ⌊ n ∣ Q ⌋ᵀ} →
    Tm m ((Q ⟦▷⟧ T) ∶ {! wk ? T  !})


_⟦▷⟧_ {m = ty q} {n = _}(Γ , T) R = (Γ ▷ R) , T
_⟦▷⟧_ {m = ex _} {n = ki} ((Γ , k) , T) R = ((Γ ▷ R) , k) , wk T R 
_⟦▷⟧_ {m = ex _} {n = ty _} ((Γ , k) , T) R = ((Γ ▷ R) , k) , wk {n = ty _} T R


wk = {!   !}

-- _∶_ {m = ex q} {Q} Γ R = Q , R 
-- _∶_ {m = ty q} Γ Q = Γ , Q

_ : Tm (ty 0) (• , *)
_ = {!  zero {Γ = •} !}

-- _ : Tm (ty 0) ((• ▷ *) , *)
-- _ = zero {Γ = •}