{-# OPTIONS --rewriting --local-confluence-check #-}
module alt where

open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

infix   3  _∋_
infix   3  _⊢_
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

data Ty : Set where
  o    : Ty
  _⇒_  : Ty → Ty → Ty

data Con : Set where
  •    : Con
  _▷_  : Con → Ty → Con

variable
  A B C : Ty
  Γ Δ Θ : Con  

-- Change 1: variables and terms are separated
ITyped = Con → Ty → Set

data _∋_ : ITyped where 
  zero  :  Γ ▷ A ∋ A
  suc   :  Γ ∋ A → (B : Ty) 
        →  Γ ▷ B ∋ A

data _⊢_ : ITyped where 
  `_   :  Γ ∋ A → Γ ⊢ A
  _·_  :  Γ ⊢ A ⇒ B → Γ ⊢ A →  Γ ⊢ B
  ƛ_   :  Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B  

data Sort : Set where 
  V T : Sort

variable
  q r s : Sort

img : Sort → ITyped  
img V = _∋_
img T = _⊢_

_⊢[_]_ : Con → Sort → Ty → Set 
Γ ⊢[ s ] A = img s Γ A 

-- Change 1: substitutions are functions 
-- and most importantly they map from Γ to Δ (the other way around "knots my brain")
_⊩[_]_ : Con → Sort → Con → Set 
Γ ⊩[ s ] Δ = ∀ A → Γ ∋ A → Δ ⊢[ s ] A

variable
  i j k    : Γ ⊢[ V ] A
  t u v    : Γ ⊢[ T ] A
  x y z    : Γ ⊢[ q ] A
  xs ys zs : Γ ⊩[ q ] Δ  

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

tm⊑ : Γ ⊢[ q ] A → Γ ⊢ A
tm⊑ {q = T} x  = x
tm⊑ {q = V} i  = ` i

tm⊒ : Γ ∋ A → Γ ⊢[ q ] A
tm⊒ {q = T} x  = ` x
tm⊒ {q = V} x  = x

-- both works! (in contrast to section 3.1) 

-- version 1: ultimately used in the paper
-- id-poly : Γ ⊩[ q ] Γ
-- id-poly = tm⊒  

-- id : Γ ⊩[ V ] Γ
-- id {Γ} = id-poly {Γ} {V} 

-- version 2: originally rejected by the termination checker 
id : Γ ⊩[ V ] Γ
id _ x = x

_,_ : Γ ⊩[ q ] Δ → Δ ⊢[ q ] A → Γ ▷ A ⊩[ q ] Δ  
(xs , x) _ zero      = x
(xs , x) _ (suc i B) = xs _ i

zero[_] : ∀ q → Γ ▷ A ⊢[ q ] A
zero[ V ]      =  zero
zero[ T ]      =  ` zero

-- behold: the main trick! hide dependence in instance resolution.
record Wk (q : Sort) : Set where
  field 
    wk : ∀ {Γ} {A} B → Γ ⊢[ q ] A → (Γ ▷ B) ⊢[ q ] A

open Wk {{...}}

_⁺_ : {{_ : Wk q}} → Γ ⊩[ q ] Δ → (A : Ty) → Γ ⊩[ q ] Δ ▷ A
(Γ ⁺ A) _ x      = wk _ (Γ _ x)

_^_ : {{_ : Wk q}} → Γ ⊩[ q ] Δ → ∀ A → Γ ▷ A ⊩[ q ] Δ ▷ A
(xs ^ A) = xs ⁺ A , zero[ _ ]

_[_] : {{_ : Wk r}} → Γ ⊢[ q ] A → Γ ⊩[ r ] Δ → Δ ⊢[ q ⊔ r ] A
_[_] {q = V} x       xs = xs _ x
_[_] {q = T} (` x)   xs = tm⊑ (xs _ x)
_[_] {q = T} (t · u) xs = (t [ xs ]) · (u [ xs ])
_[_] {q = T} (ƛ t)   xs = ƛ (t [ xs ^ _ ])

-- this instance grantees that the instance arguments from above always get resolved.
-- ensuring now "harm" is done later on
instance 
  inst : Wk q 
  inst {V} = record { wk = λ B x → suc x B  } 
  -- this one uses inst {V} ...
  inst {T} = record { wk = λ B x → x [ id ⁺ _ ] } 

suc[_]  :  ∀ q → Γ ⊢[ q ] B → ∀ A 
        →  Γ ▷ A ⊢[ q ] B
suc[ V ] i  A  = suc i A
suc[ T ] t  A  = t [ id ⁺  A ]

_∘_ : Γ ⊩[ q ] Δ → Δ ⊩[ r ] Θ → Γ ⊩[ q ⊔ r ] Θ
(xs ∘ ys) _ x = (xs _ x) [ ys ]

-- from here some of the proofs change, because we use the encoding via functions 
⁺-nat[]v : {i : Γ ⊢[ V ] B}{xs : Γ ⊩[ q ] Δ} → i [ xs ⁺ A ] ≡ suc[ q ] (i [ xs ]) A
⁺-nat[]v {q = V} = refl 
⁺-nat[]v {q = T} = refl

-- and somehow agda's implicit argument inference gets worse, hm...
-- without type annotations (as can be seen in the paper) this produces:
-- _x.Γ_439 : Con
-- _x.q_440 : Sort
-- _x.A_441 : Ty
-- _Γ_442 : Con
-- _q_443 : Sort
-- _A_444 : Ty
-- _445 : Wk V
-- _446 : _Γ_442 ⊢[ _q_443 ] _A_444
-- _447 : img _q_443 _Γ_442 _A_444
-- Failed to solve the following constraints:
--   Check definition of [id] : {x : _x.Γ_439 ⊢[ _x.q_440 ] _x.A_441} →
--                              _446 [ id ] ≡ _447
--     stuck because
--       /home/weidner/proglang/research/agda/cp/alt.lagda:160.11-15: error: [SplitError.BlockedType]
--       Cannot split on argument of unresolved type
--       _x.Γ_439 ⊢[ _x.q_440 ] _x.A_441
--       when checking that the pattern zero has type
--       _x.Γ_439 ⊢[ _x.q_440 ] _x.A_441
--     (blocked on _x.q_440)
--   Resolve instance argument _432 : Wk V No candidates yet
--     (blocked on _x.q_440)
--
-- this is clearly rubbish: no candidates for Wk V? i have a blanket implementation!


-- todo: avoid fun-ext (by the standard trick)
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
postulate
  fun-ext : ∀{ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂
  fun-exti : ∀{ℓ₁ ℓ₂} → ExtensionalityImplicit  ℓ₁ ℓ₂

ext : id {Γ = Γ} ^ A ≡ id 
ext = fun-ext (λ _ → fun-ext λ { zero → refl; (suc x B) → refl })

[id] : {x : Γ ⊢[ q ] A} → x [ id ] ≡ x
[id] {q = V} {x = zero}     = refl
[id] {q = V} {x = suc i A}  = 
   i [ id ⁺ A ]  ≡⟨ ⁺-nat[]v {i = i} {xs = id} ⟩
   suc (i [ id ]) A
   ≡⟨ cong (λ j → suc j A) ([id] {x = i}) ⟩      
   suc i A       ∎
[id] {q = T} {x = ` i}    =
   cong `_ ([id] {x = i})
[id] {q = T} {x = t · u}  =
   cong₂ _·_ ([id] {x = t}) ([id] {x = u})
[id] {q = T} {x = ƛ t} =
   cong ƛ_ (_ ≡⟨ cong (t [_]) ext ⟩ ([id] {x = t}))

-- todo: avoid fun-ext
∘id : {xs : Γ ⊩[ q ] Δ} → xs ∘ id ≡ xs
∘id = fun-ext (λ _ → fun-ext (λ { x → [id] }))

id∘ : {xs : Γ ⊩[ q ] Δ} → id ∘ xs ≡ xs
id∘ = refl

⁺∘ : {xs : Γ ⊩[ q ] Δ} {ys : Δ ⊩[ q ] Θ}  → xs ⁺ A ∘ (ys , x) ≡ xs ∘ ys
⁺∘ = fun-ext (λ _ → fun-ext λ { x → {!   !} })