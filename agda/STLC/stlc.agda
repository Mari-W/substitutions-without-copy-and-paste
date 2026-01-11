{-# OPTIONS --rewriting --local-confluence-check #-}
module stlc where 

open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning public
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
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

data Sort : Set where 
  V T : Sort

data Mode : Set where
  ex su : Sort → Mode
  ty cx : Mode

variable
  q r s : Sort
  m n  : Mode


⟦_⟧ : Mode → Set
data Tm : (m : Mode) → ⟦ m ⟧ → Set   

⟦ ty ⟧ = ⊤
⟦ cx ⟧ = ⊤
⟦ ex _ ⟧ = Tm cx tt × Tm (ty) tt
⟦ su _ ⟧ = Tm cx tt × Tm cx tt

Con : Set
Con = Tm cx tt
Ty : Set 
Ty = Tm (ty) tt

_⊢[_]_ : Con → Sort → Ty → Set 
Γ ⊢[ q ] A = Tm (ex q) (Γ , A)  

_⊩[_]_ : Con → Sort → Con → Set
Γ ⊩[ q ] Δ = Tm (su q) (Γ , Δ)  

variable
  A B C : Ty
  Γ Δ Θ : Con  
  i j k : Γ ⊢[ V ] A
  t u v : Γ ⊢[ T ] A
  x y z : Γ ⊢[ q ] A
  X Y Z : ⟦ m ⟧

data Tm where
  o     : Ty
  _⇒_   : Ty → Ty → Ty 

  •     : Con
  _▷_   : Con → Ty → Con

  zero  : (Γ ▷ A) ⊢[ V ] A  
  suc   : Γ ⊢[ V ] A → (B : Ty) → Γ ▷ B  ⊢[ V ]  A

  `_    : Γ ⊢[ V ] A → Γ  ⊢[ T ]  A
  _·_   : Γ ⊢[ T ] A ⇒ B → Γ ⊢[ T ] A → Γ ⊢[ T ] B
  ƛ_    : Γ ▷ A ⊢[ T ] B → Γ ⊢[ T ] A ⇒ B

  ε    : Γ ⊩[ q ] •
  _,_  : Γ ⊩[ q ] Δ → Γ ⊢[ q ] A → Γ ⊩[ q ] Δ ▷ A  


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
