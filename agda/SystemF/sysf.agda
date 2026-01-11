{-# OPTIONS --rewriting --local-confluence-check #-}
module sysf where 

open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning public
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (¬_)
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

data Sort : Set 
data IsV : Sort → Set 

data Sort where
  V    : Sort
  T>V  : (s : Sort) → IsV s → Sort

data IsV where
    isV : IsV V

pattern T = T>V V isV

variable
  q r s : Sort

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

data Mode : Set where
  ki ty ex : Mode 

variable
  m n : Mode 
  
⟦_⟧ : Mode → Set
data Tm : (s : Sort) (m : Mode) → ⟦ m ⟧ → Set   

data Con : Set 

⟦ ex ⟧ = ∃[ Γ ] Tm T ty Γ
⟦ ty ⟧ = Con
⟦ ki ⟧ = ⊤

⋆ = Tm T ki tt

_⊢[_] : Con → Sort → Set
Γ ⊢[ q ] = Tm q ty Γ

_⊢ = _⊢[ T ]

_⊢[_]_ : (Γ : Con) → Sort → Γ ⊢ → Set 
Γ ⊢[ q ] A = Tm q ex (Γ , A)  

_⊢_ = _⊢[ T ]_

_↑ᵀ : Mode → Mode 
ki   ↑ᵀ = ki
ty   ↑ᵀ = ki
ex   ↑ᵀ = ty 

⌊_⌋ᵀ : Con → ⟦ m ↑ᵀ ⟧ 
⌊_⌋ᵀ {m = ki} _ = tt
⌊_⌋ᵀ {m = ty} _ = tt
⌊_⌋ᵀ {m = ex} Γ = Γ

_⊢[_∣_]ᵀ : Con → Sort → Mode → Set 
Γ ⊢[ q ∣ m ]ᵀ = Tm q (m ↑ᵀ) ⌊ Γ ⌋ᵀ 

_⊢[_]ᵀ : Con → Mode → Set 
Γ ⊢[ m ]ᵀ = Γ ⊢[ T ∣ m ]ᵀ

data Con where
  •      : Con
  _▷[_]_ : (Γ : Con) (m : Mode) → Γ ⊢[ m ]ᵀ → Con

pattern _▷tt Γ  = Γ ▷[ ty ] tt
pattern _▷_ Γ A =  Γ ▷[ ex ] A

variable
  Γ Δ Θ : Con  
  A B C : Γ ⊢[ T ]
  i j k : Γ ⊢[ V ] A
  e f : Γ ⊢[ T ] A
  x z : Γ ⊢[ q ] A
  Q R S : Γ ⊢[ q ∣ m ]ᵀ

⌊_⌋ : Γ ⊢[ m ]ᵀ → ⟦ m ⟧ 
⌊_⌋ {m = ki}     _ = tt
⌊_⌋ {Γ} {m = ty} _ = Γ 
⌊_⌋ {m = ex}     Q = _ , Q

_⊢[_∣_]_ : (Γ : Con) → (s : Sort) (m : Mode) → Γ ⊢[ m ]ᵀ → Set 
Γ ⊢[ s ∣ m ] Q = Tm s m ⌊ Q ⌋

variable
  X Y Z : Γ ⊢[ q ∣ m ] Q

{- record Sucᵀ (m : Mode) : Set where
  inductive
  field 
    wkᵀ : Γ ⊢[ m ]ᵀ → ∀ R → (Γ ▷[ n ] R) ⊢[ m ]ᵀ
    wk : {{_ : Sucᵀ m}} → {Q : Γ ⊢[ m ]ᵀ} → Γ ⊢[ q ∣ m ]ᵀ Q → ∀ R → (Γ ▷[ n ] R) ⊢[ q ∣ m ]ᵀ wkᵀ Q R
  
open Sucᵀ {{...}}
 -}

wkᵀ : Γ ⊢[ m ]ᵀ → ∀ R → (Γ ▷[ n ] R) ⊢[ m ]ᵀ
data Tm where
  `[_]_    : {Q : Γ ⊢[ m ]ᵀ} → 
    ¬ (m ≡ ki) → 
    Γ ⊢[ V ∣ m ] Q → 
    Γ ⊢[ T ∣ m ] Q
  zero  : {Q : Γ ⊢[ m ]ᵀ} → 
    ¬ (m ≡ ki) → 
    (Γ ▷[ m ] Q) ⊢[ V ∣ m ] wkᵀ Q Q
  suc   : {Q : Γ ⊢[ m ]ᵀ} → 
    ¬ (m ≡ ki) → 
    Γ ⊢[ V ∣ m ] Q → 
    (Γ ▷[ n ] R) ⊢[ V ∣ m ] wkᵀ Q R

  *     : ⋆

  o     : Γ ⊢
  _⇒_   : Γ ⊢ → Γ ⊢ → Γ ⊢

  _·_   : Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
  ƛ_    : (Γ ▷ A) ⊢ wkᵀ B A → Γ ⊢ (A ⇒ B) 

data _⊩[_]_ : Con → Sort → Con → Set 
_[_]ᵀ : Γ ⊢[ q ∣ m ]ᵀ → Δ ⊩[ r ] Γ → Δ ⊢[ q ⊔ r ∣ m ]ᵀ 

data _⊩[_]_ where
  ε    : Γ ⊩[ q ] •
  _,_  : (σ : Γ ⊩[ q ] Δ) → Γ ⊢[ q ∣ m ] (Q [ σ ]ᵀ) → Γ ⊩[ q ] Δ ▷[ m ] Q

variable
  σ δ : Δ ⊩[ r ] Γ

tm⊑ : q ⊑ s → Γ ⊢[ q ∣ m ] Q → Γ ⊢[ s ∣ m ] Q
tm⊑ rfl x  = x
tm⊑ {m = ki} v⊑t (zero prf)  with () ← prf refl
tm⊑ {m = ki} v⊑t (suc prf _) with () ← prf refl
tm⊑ {m = ty} {Q = Q} v⊑t i = `[_]_ {Q = Q} (λ ()) i
tm⊑ {m = ex} v⊑t i = `[ (λ ()) ] i  

_^_ : (σ : Γ ⊩[ q ] Δ) → ∀ Q → Γ ▷ (Q [ σ ]ᵀ) ⊩[ q ] Δ ▷ Q 

wkᵀ Q = {!   !}

_[_]ᵀ {m = ki} * σ = *
_[_]ᵀ {m = ty} * σ = *
_[_]ᵀ {m = ki} (zero prf) _            with () ← prf refl
_[_]ᵀ {m = ty} (zero prf) _            with () ← prf refl
_[_]ᵀ {m = ki} (suc prf _) _           with () ← prf refl
_[_]ᵀ {m = ty} (suc prf _) _           with () ← prf refl
_[_]ᵀ {m = ki} (`[ prf ] _) σ          with () ← prf refl
_[_]ᵀ {m = ty} (`[ prf ] _) σ          with () ← prf refl 
_[_]ᵀ {m = ex} (`[_]_ {Q = Q} prf x) σ = tm⊑ {Q = Q} ⊑t (x [ σ ]ᵀ)
_[_]ᵀ {m = ex} (zero _) (σ , x)        = x
_[_]ᵀ {m = ex} (suc _ x) (σ , _)       = x [ σ ]ᵀ
_[_]ᵀ {m = ex} o       σ = o
_[_]ᵀ {m = ex} (A ⇒ B) σ = (A [ σ ]ᵀ) ⇒ (B [ σ ]ᵀ)

postulate
  wk[] : {R : Γ ⊢[ T ∣ n ]ᵀ} {Q : Γ ⊢[ m ]ᵀ} {σ :  Δ ⊩[ r ] Γ} {x : Δ ⊢[ r ∣ n ] (R [ σ ]ᵀ)} → 
    wkᵀ Q R [ σ , x ]ᵀ ≡ Q [ σ ]ᵀ  
-- {-# REWRITE wk[] #-}

_[_] : {Q : Γ ⊢[ T ∣ m ]ᵀ} → Γ ⊢[ q ∣ m ] Q → (σ : Δ ⊩[ r ] Γ) → Δ ⊢[ q ⊔ r ∣ m ] (Q [ σ ]ᵀ)
_[_] {m = ex} (`[ prf ] x) σ = tm⊑ ⊑t (x [ σ ])
_[_] {m = ex} (zero prf) (σ , x) = {! x  !}
_[_] {m = ex} (suc prf x) (σ , _) = {! x [ σ ]  !}
_[_] {m = ex} (t₁ · t₂) σ = {!   !}
_[_] {m = ex} (ƛ t) σ = {!   !}
_[_] {m = ki} {q = q} {Q = Q} t σ = _[_]ᵀ {q = q} {m = ty} {! t  !} σ
_[_] {m = ty} {Q = Q} t σ = {!   !}

lem : (m ↑ᵀ) ↑ᵀ ≡ ki 
lem {ki} = refl
lem {ty} = refl
lem {ex} = refl
{-# REWRITE lem #-}


lem₁ : {R : Γ ⊢[ T ∣ m ↑ᵀ ]ᵀ} → ⌊_⌋ {Γ = Γ} R ≡ ⌊_⌋ᵀ {m = m} Γ 
lem₁ {m = ki} = refl
lem₁ {m = ty} = refl
lem₁ {m = ex} = refl
{-# REWRITE lem₁ #-}

coincidence : {Q : Γ ⊢[ q ∣ m ]ᵀ} → {σ : Δ ⊩[ r ] Γ} →
   Q [ σ ]ᵀ ≡ _[_] {Q = *} Q σ
coincidence {m = ki} = refl
coincidence {m = ty} = refl 
coincidence {m = ex} = refl

  -- ε     : Γ ⊩[ q ] •
  
  -- _,_   : {A : Γ ⊢[ T ]} →
  --   Γ ⊩[ q ] Δ → Γ ⊢[ m ]ᵀ Q → Γ ⊩[ q ] (Δ ▷[ m ] {! Q !}) 

-- _⊩[_]_ : Con → Sort → Con → Set
-- Γ ⊩[ q ] Δ = Tm (su q) (Γ , Δ)  

{-
foo : Γ ⊢[ ex q ]ᵀ Q → Set 
foo t = {! t !} -}
 
{- data _⊑_ : Sort → Sort → Set where
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
 -}