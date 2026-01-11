{-# OPTIONS --rewriting --local-confluence-check #-}
module subst where

open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

open import naive using (Ty ;  o ; _⇒_ ; • ; _▷_ ; Con) public 

variable
  A B C : Ty
  Γ Δ Θ : Con  

infix   3  _⊢[_]_
infix   3  _⊩[_]_
infixl  4  _,_
infix   5  _∘_
infix   5  ƛ_
infixl  6  _·_
infix   7  `_
infix   8  _^_
infix   8  _⁺_
infix   8  _[_]

module Subst where

data Sort : Set where 
  V T : Sort

variable
  q r s    : Sort

data _⊢[_]_ : Con → Sort → Ty → Set where
  zero  : Γ ▷ A ⊢[ V ] A
  suc   : Γ  ⊢[ V ]  A → (B : Ty) → Γ ▷ B  ⊢[ V ]  A
  `_    : Γ  ⊢[ V ]  A → Γ  ⊢[ T ]  A
  _·_   : Γ ⊢[ T ] A ⇒ B → Γ ⊢[ T ] A → Γ ⊢[ T ] B
  ƛ_    : Γ ▷ A ⊢[ T ] B → Γ ⊢[ T ] A ⇒ B

data _⊩[_]_ : Con → Sort → Con → Set where
  ε    : Γ ⊩[ q ] •
  _,_  : Γ ⊩[ q ] Δ → Γ ⊢[ q ] A → Γ ⊩[ q ] Δ ▷ A  

variable
  i j k    : Γ ⊢[ V ] A
  t u v    : Γ ⊢[ T ] A
  x y z : Γ ⊢[ q ] A
  xs ys zs : Γ ⊩[ q ] Δ  

data _⊑_ : Sort → Sort → Set where
  rfl  : s ⊑ s
  v⊑t  : V ⊑ T

_⊔_ : Sort → Sort → Sort
V ⊔ r  =  r
T ⊔ r  =  T

⊑t   : s ⊑ T
v⊑   : V ⊑ s
⊑q⊔  : q ⊑ (q ⊔ r)
⊑⊔r  : r ⊑ (q ⊔ r)

⊔⊔  : q ⊔ (r ⊔ s) ≡ (q ⊔ r) ⊔ s
⊔v  : q ⊔ V ≡ q
⊔t  : q ⊔ T ≡ T

⊑t {V} = v⊑t
⊑t {T} = rfl

v⊑ {V} = rfl
v⊑ {T} = v⊑t

⊑q⊔ {V} = v⊑
⊑q⊔ {T} = rfl

⊑⊔r {q = V} = rfl
⊑⊔r {q = T} = ⊑t

⊔⊔ {V} = refl
⊔⊔ {T} = refl

⊔v {V} = refl
⊔v {T} = refl

⊔t {V} = refl
⊔t {T} = refl

{-# REWRITE ⊔⊔ ⊔v ⊔t #-} 

zero[_] : ∀ q → Γ ▷ A ⊢[ q ] A
zero[ V ]      =  zero
zero[ T ]      =  ` zero

tm⊑ : q ⊑ s → Γ ⊢[ q ] A → Γ ⊢[ s ] A
tm⊑ rfl x  = x
tm⊑ v⊑t i  = ` i

-- [MW] behold: the main trick! hide dependence in instance resolution.
record Suc (q : Sort) : Set where
  field 
    wk : Γ ⊢[ q ] B → ∀ A → Γ ▷ A ⊢[ q ] B

open Suc {{...}}

_⁺_ : {{_ : Suc q}} → Γ ⊩[ q ] Δ → (A : Ty) → Γ ▷ A ⊩[ q ] Δ
ε ⁺ A = ε
(xs , x) ⁺ A = xs ⁺ A , wk x A

_^_ : {{_ : Suc q}} → Γ ⊩[ q ] Δ → ∀ A → Γ ▷ A ⊩[ q ] Δ ▷ A
xs ^ A =  xs ⁺ A , zero[ _ ]

_[_] : {{_ : Suc r}} → Γ ⊢[ q ] A → Δ ⊩[ r ] Γ → Δ ⊢[ q ⊔ r ] A
zero       [ xs , x ]  = x 
(suc i _)  [ xs , x ]  = i [ xs ]
(` i)      [ xs ]      = tm⊑  ⊑t  (i [ xs ])
(t · u)    [ xs ]      = (t [ xs ]) · (u [ xs ])
(ƛ t)      [ xs ]      = ƛ (t [ xs ^ _ ]) 

-- id-poly : {{_ : Suc q}} → Γ ⊩[ q ] Γ 
-- id-poly {Γ = •} = ε
-- id-poly {Γ = Γ ▷ A} = id-poly ^ A
-- 
-- id : {{_ : Suc V}} → Γ ⊩[ V ] Γ 
-- id = id-poly
-- {-# INLINE id #-}

-- [MW] this now works ... (ref sec 3.1)
id : {{_ : Suc V}} → Γ ⊩[ V ] Γ
id {Γ = •} = ε
id {Γ = xs ▷ x} = id ^ _

-- [MW] this instance effectively grantees that the 
-- instance arguments from above always get resolved.
-- thinking about hiding this in its own module, for clarity..
instance 
  V<T : Suc q 
  V<T {V} = record { wk = suc } 
  -- the second uses the first clause.. 
  V<T {T} = record { wk = λ x _ → x [ id ⁺ _ ] } 

-- [MW] syntax 
suc[_] : ∀ q → Γ ⊢[ q ] B → ∀ A → Γ ▷ A ⊢[ q ] B
suc[_] _ = wk

_∘_ : Γ ⊩[ q ] Θ → Δ ⊩[ r ] Γ → Δ ⊩[ q ⊔ r ] Θ
ε ∘ ys         = ε
(xs , x) ∘ ys  = (xs ∘ ys) , x [ ys ]
