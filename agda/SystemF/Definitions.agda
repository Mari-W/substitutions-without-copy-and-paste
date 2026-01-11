{-# OPTIONS --rewriting --local-confluence-check #-}
module SystemF.Definitions where

open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; module ≡-Reasoning) public
open ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

-- fixities --------------------

infix   3  _⊢[_]
infix   3  _⊢[_]_
infix   3  _⊢[_∣_]ᵀ 
infix   3  _⊢[_∣_]_
infix   3  _⊩[_]_
infixl  4  _,_
infix   5  _∘_
infix   5  ƛ_
infixl  6  _·_
infix   7  `_
infix   8  _⁺_
infix   8  _↑_
infix   8  _[_]ᵀ
infix   8  _[_]

data Sort : Set where 
  V E : Sort

data Mode : Set where 
  T K : Mode

variable
  m n o : Mode
  q r s : Sort

_⊔_ : Sort → Sort → Sort
V ⊔ r  =  r
E ⊔ r  =  E

⊔⊔  : q ⊔ (r ⊔ s) ≡ (q ⊔ r) ⊔ s
⊔v  : q ⊔ V ≡ q
⊔t  : q ⊔ E ≡ E

⊔⊔ {V} = refl
⊔⊔ {E} = refl

⊔v {V} = refl
⊔v {E} = refl

⊔t {V} = refl
⊔t {E} = refl
{-# REWRITE ⊔⊔ ⊔v ⊔t #-} 

data Con : Set 
data _⊢[_]  : Con → Sort → Set

_⊢ : Con → Set
Γ ⊢ = Γ ⊢[ E ]

_⊢[_∣_]ᵀ : Con → Sort → Mode → Set
Γ ⊢[ q ∣ K ]ᵀ = ⊤
Γ ⊢[ q ∣ T ]ᵀ = Γ ⊢[ q ]

_⊢[_]ᵀ : Con → Mode → Set 
Γ ⊢[ m ]ᵀ = Γ ⊢[ E ∣ m ]ᵀ

variable 
  Γ Δ Θ : Con
  α β γ : Γ ⊢[ V ]
  A B C : Γ ⊢[ E ]
  X Y Z : Γ ⊢[ q ]
  Q R S : Γ ⊢[ q ∣ m ]ᵀ

data _⊢[_]_ : (Γ : Con) → Sort → Γ ⊢ → Set
data _⊩[_]_ : Con → Sort → Con → Set

_⊢[_∣_]_ : (Γ : Con) → Sort → (m : Mode) → Γ ⊢[ m ]ᵀ → Set
Γ ⊢[ q ∣ K ] Q = Γ ⊢[ q ]
Γ ⊢[ q ∣ T ] Q = Γ ⊢[ q ] Q

data Con where
  •    : Con
  _▷[_]_  : (Γ : Con) → (m : Mode) → Γ ⊢[ m ]ᵀ → Con

pattern _▷tt Γ  = Γ ▷[ K ] tt
pattern _▷_ Γ A =  Γ ▷[ T ] A

record Sucᵀ (q : Sort) (m : Mode) : Set where
  inductive
  field
    wkᵀ : Γ ⊢[ q ∣ m ]ᵀ → ∀ Q → Γ ▷[ n ] Q ⊢[ q ∣ m ]ᵀ

open Sucᵀ {{...}}

data _⊢[_] where
  zero : Γ ▷tt ⊢[ V ]
  suc  : Γ ⊢[ V ] → Γ ▷tt ⊢[ V ]
  `_   : Γ ⊢[ V ] → Γ ⊢[ E ]

  𝕠    : Γ ⊢[ E ]
  _⇒_  : Γ ⊢[ E ] → Γ ⊢[ E ] → Γ ⊢[ E ]
  ∀α_  : (Γ ▷tt ⊢[ E ]) → Γ ⊢[ E ]

data _⊢[_]_ where
  zero  : {{_ : Sucᵀ E T}} → Γ ▷ A ⊢[ V ] wkᵀ A A
  suc   : {{_ : Sucᵀ E T}} → Γ ⊢[ V ] A → (B : Γ ⊢[ E ]) → Γ ▷ B ⊢[ V ] wkᵀ B B

  `_    : Γ  ⊢[ V ]  A → Γ ⊢[ E ]  A
  _·_   : Γ ⊢[ E ] A ⇒ B → Γ ⊢[ E ] A → Γ ⊢[ E ] B
  ƛ_    : {{_ : Sucᵀ E T}} → Γ ▷ A ⊢[ E ] wkᵀ B A → Γ ⊢[ E ] A ⇒ B 

variable
  i j k : Γ ⊢[ V ] A
  t u v : Γ ⊢[ E ] A
  x y z : Γ ⊢[ q ] A

record Suc (q : Sort) (m : Mode) : Set where
  field
    wk : {{_ : Sucᵀ E m}} {R : Γ ⊢[ m ]ᵀ} → 
      Γ ⊢[ q ∣ m ] R → ∀ Q → Γ ▷[ n ] Q ⊢[ q ∣ m ] wkᵀ R Q

open Suc {{...}}

_[_]ᵀ : {{_ : Sucᵀ r m}} → Γ ⊢[ q ∣ m ]ᵀ → Δ ⊩[ r ] Γ → Δ ⊢[ q ⊔ r ∣ m ]ᵀ 
data _⊩[_]_ where
  ε    : Γ ⊩[ q ] •
  _,_  : ∀ {{_ : Sucᵀ q m}} {{_ : Sucᵀ E m}} {{_ : Suc q m}} {Q : Δ ⊢[ m ]ᵀ} → 
    (σ : Γ ⊩[ q ] Δ) → Γ ⊢[ q ∣ m ] Q [ σ ]ᵀ → Γ ⊩[ q ] Δ ▷[ m ] Q

_⁺_ : Γ ⊩[ q ] Δ → ∀ Q → Γ ▷[ m ] Q ⊩[ q ] Δ 
ε ⁺ A        = ε
(xs , x) ⁺ Q = xs ⁺ Q , {! wk x Q  !}

_[_]ᵀ {m = K} {q = q} _ _             = tt 
_[_]ᵀ {m = T} {q = q} zero (σ , x)    = x
_[_]ᵀ {m = T} {q = q} (suc x) (σ , _) = x [ σ ]ᵀ 
_[_]ᵀ {m = T} {q = q} (` x) σ         = {! x [ σ ]ᵀ  !}
_[_]ᵀ {m = T} {q = q} 𝕠 σ             = 𝕠
_[_]ᵀ {m = T} {q = q} (A ⇒ B) σ       = (A [ σ ]ᵀ) ⇒ (B [ σ ]ᵀ)
_[_]ᵀ {m = T} {q = q} (∀α t) σ        = {!   !}

_[_] : {{_ : Sucᵀ r m}} → Γ ⊢[ q ∣ m ] Q → (σ : Δ ⊩[ r ] Γ) → Δ ⊢[ q ⊔ r ∣ m ] Q [ σ ]ᵀ

variable
  σ δ τ : Γ ⊩[ q ] Δ  


-- _[_] : {Q : ty m Γ} → 
--   Γ ⊢[ q , m ] Q → (σ : Γ ⊩[ r ] Δ) → Δ ⊢[ q ⊔ r , m ] (Q [ σ ]ty)


-- substitutions --------------------

{- -- change 1: no substitutions as vectors
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

 -}