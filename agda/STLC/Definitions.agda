{-# OPTIONS --rewriting --local-confluence-check #-}
module STLC.Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; module ≡-Reasoning) public
open ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

-- fixities --------------------

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

-- syntax --------------------

data Ty : Set where
  ⊤    : Ty
  _⇒_  : Ty → Ty → Ty
 
data Con : Set where
  •    : Con
  _▷_  : Con → Ty → Con

-- change 1: no weird sort that 
-- hides the dependency structure
data Sort : Set where 
  V T : Sort

variable
  q r s : Sort

variable
  A B C : Ty
  Γ Δ Θ : Con  

data _⊢[_]_ : Con → Sort → Ty → Set where
  zero  : Γ ▷ A ⊢[ V ] A
  suc   : Γ ⊢[ V ] A → (B : Ty) → Γ ▷ B  ⊢[ V ]  A
  `_    : Γ ⊢[ V ] A → Γ  ⊢[ T ]  A
  _·_   : Γ ⊢[ T ] A ⇒ B → Γ ⊢[ T ] A → Γ ⊢[ T ] B
  ƛ_    : Γ ▷ A ⊢[ T ] B → Γ ⊢[ T ] A ⇒ B

-- substitutions --------------------

-- change 1: no substitutions as vectors
-- instead use functions
_⊩[_]_ : Con → Sort → Con → Set 
Γ ⊩[ s ] Δ = ∀ A → Γ ⊢[ V ] A → Δ ⊢[ s ] A

-- mirror the data type constructors from before..
ε : • ⊩[ q ] Δ
ε _ ()

_,_ : Γ ⊩[ q ] Δ → Δ ⊢[ q ] A → Γ ▷ A ⊩[ q ] Δ  
(xs , x) _ zero      = x
(xs , x) _ (suc i B) = xs _ i

variable
  i j k : Γ ⊢[ V ] A
  t u v : Γ ⊢[ T ] A
  x y z : Γ ⊢[ q ] A
  γ δ σ : Γ ⊩[ q ] Δ  

-- kit order --------------------

_⊔_ : Sort → Sort → Sort
V ⊔ r  =  r
T ⊔ r  =  T

⊔⊔  : q ⊔ (r ⊔ s) ≡ (q ⊔ r) ⊔ s
⊔v  : q ⊔ V ≡ q
⊔t  : q ⊔ T ≡ T

⊔⊔ {V} = refl
⊔⊔ {T} = refl

⊔v {V} = refl
⊔v {T} = refl

⊔t {V} = refl
⊔t {T} = refl

{-# REWRITE ⊔⊔ ⊔v ⊔t #-} 

zero[_] : ∀ q → Γ ▷ A ⊢[ q ] A
zero[ V ] =  zero
zero[ T ] =  ` zero

-- change 3: remove _⊑_ .. in favor of 
-- pattern matching
tm⊑ : Γ ⊢[ q ] A → Γ ⊢[ T ] A
tm⊑ {q = T} x  = x
tm⊑ {q = V} i  = ` i

tm⊒ : Γ ⊢[ V ] A → Γ ⊢[ q ] A
tm⊒ {q = T} x  = ` x
tm⊒ {q = V} x  = x

-- traversal --------------------

-- change 4: hide structural dependency in 
-- instance resolution
record Suc (q : Sort) : Set where
  field 
    wk : Γ ⊢[ q ] B → ∀ A → Γ ▷ A ⊢[ q ] B

open Suc {{...}}

_⁺_ : {{_ : Suc q}} → Γ ⊩[ q ] Δ → (A : Ty) → Γ ⊩[ q ] Δ ▷ A
(σ ⁺ A) _ x = wk (σ _ x) A 

_↑_ : {{_ : Suc q}} → Γ ⊩[ q ] Δ → ∀ A → Γ ▷ A ⊩[ q ] Δ ▷ A
σ ↑ A = σ ⁺ A , zero[ _ ]

_[_] : {{_ : Suc r}} → Γ ⊢[ q ] A → Γ ⊩[ r ] Δ → Δ ⊢[ q ⊔ r ] A
_[_] {q = V} x σ  = σ _ x
(` i)   [ σ ] = tm⊑ (i [ σ ])
(t · u) [ σ ] = (t [ σ ]) · (u [ σ ])
(ƛ t)   [ σ ] = ƛ (t [ σ ↑ _ ]) 

id[_] : ∀ q → {{_ : Suc q}} → Γ ⊩[ q ] Γ
id[_] _ _ x = tm⊒ x

-- ... right here! the second clause depends
-- on the first clause 
instance 
  V<T : Suc q 
  V<T {V} = record { wk = suc } 
  V<T {T} = record { wk = λ x _ → x [ id[ V ] ⁺ _ ] } 

suc[_] : ∀ q → Γ ⊢[ q ] B → ∀ A → Γ ▷ A ⊢[ q ] B
suc[_] _ = wk

-- composition --------------------

_∘_ : Γ ⊩[ q ] Δ → Δ ⊩[ r ] Θ → Γ ⊩[ q ⊔ r ] Θ
(σ ∘ δ) _ x = (σ _ x) [ δ ]

