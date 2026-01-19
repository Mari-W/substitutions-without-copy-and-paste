{-# OPTIONS --rewriting --local-confluence-check #-}
module  sysf where 

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

Matrix = ℕ × ℕ × ℕ × ℕ × ℕ 

        -- VarTm / Bind / Termination / Weaken / Ctx
data Mode : Matrix → Set where
  ex : (q : ℕ) → Mode (q , 1 , 1 , 1 , 0) 
  ty : (q : ℕ) → Mode (q , 1 , 0 , 1 , 1)
  su : (q : ℕ) → Mode (q , 0 , 1 , 1 , 0)
  cx : Mode (2 , 0 , 0 , 0 , 0) 
  ki : Mode (2 , 0 , 0 , 0 , 1)

variable
  i j k o : ℕ
  h′ i′ j′ k′ o′ : ℕ
  M N : Matrix
  q r s : ℕ
  q′ r′ s′ : ℕ
  m n   : Mode (q , i , j , k , o) 
  -- b     : Mode (1 , j , k , o)

⟦_⟧ : Mode (q , i , j , k , o) → Set
data Tm : (m : Mode (q , i , j , k , o)) → ⟦ m ⟧ → Set   

⟦ ki   ⟧ = ⊤ 
⟦ cx   ⟧ = ⊤
⟦ su _ ⟧ = Tm cx tt × Tm cx tt
⟦ ex _ ⟧ = ∃[ Γ ] Tm (ty 1) Γ
⟦ ty _ ⟧ = Tm cx tt 

{- 
⋆ = Tm ki tt

Cx = Tm cx tt

_⊢[_] : Cx → ℕ → Set
Γ ⊢[ q ] = Tm (ty q) Γ
_⊢ = _⊢[ 1 ]

_⊩[_]_ : Cx → ℕ → Cx → Set
Γ ⊩[ q ] Δ = Tm (su q) (Γ , Δ)  

_⊢[_]_ : (Γ : Cx) → ℕ → Γ ⊢ → Set 
Γ ⊢[ q ] A = Tm (ex q) (Γ , A)  
_⊢_ = _⊢[ 1 ]_

⊢⟦_⟧_ : (m : Mode (q , i , j , k , o)) → ⟦ m ⟧ → Set 
⊢⟦ m ⟧ Q = Tm m Q

⊢⟦_∣_⟧_ : (q : ℕ) (m : Mode (q , i , j , k , o)) → ⟦ m ⟧ → Set 
⊢⟦ q ∣ m ⟧ Q = Tm m Q

⊢⦅_⦆_ : (m : Mode (q , 0 , j , k , o)) → ⟦ m ⟧ → Set 
⊢⦅ m ⦆ Q = ⊢⟦ m ⟧ Q 

⊢⟪_⟫_ : (m : Mode (q , 1 , j , k , o)) → ⟦ m ⟧ → Set 
⊢⟪ m ⟫ Q = ⊢⟦ m ⟧ Q -}

matrix : Mode M → Matrix
matrix {M} m = M

_↑ᴵ : (m : Mode (q , i , j , k , o)) → Matrix
ex x ↑ᴵ = matrix (ty 1)
ty x ↑ᴵ = matrix ki
su x ↑ᴵ = matrix ki
cx ↑ᴵ   = matrix ki
_↑ᴵ {q} {i} {j} {k} {o} ki = q , i , j , k , o

_↑ᵀ : (m : Mode (q , i , j , k , o)) → Mode (m ↑ᴵ)
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

{- ⊢⟦_⟧ᵀ_ : (m : Mode (q , i , j , k , o)) → ⟦ m ⟧ → Set 
⊢⟦ m ⟧ᵀ Q = Tm (m ↑ᵀ) ⌊ Q ⌋ᵀ

⊢⟦_∣_⟧ᵀ_ : (i : ℕ) (m : Mode (q , i , j , k , o)) → ⟦ m ⟧ → Set 
⊢⟦ i ∣ m ⟧ᵀ Q = Tm (m ↑ᵀ) ⌊ Q ⌋ᵀ

⊢⦅_⦆ᵀ_ : (m : Mode (0 , j , k , o)) → ⟦ m ⟧ → Set 
⊢⦅ m ⦆ᵀ Q = ⊢⟦ m ⟧ᵀ Q 

⊢⟪_⟫ᵀ_ : (m : Mode (1 , j , k , o)) → ⟦ m ⟧ → Set 
⊢⟪ m ⟫ᵀ Q = ⊢⟦ m ⟧ᵀ Q  -}

{- variable
  -- k : ⋆
  Γ Δ Θ : Cx
  A B C : Γ ⊢[ q ]
  σ δ τ : Γ ⊩[ q ] Δ
  -- x y z : Γ ⊢[ V ] A
  t u v : Γ ⊢[ T ] A
  x y z : Γ ⊢[ q ] A
  Q R S : ⟦ m ⟧
  X Y Z : ⊢⟦_⟧_ {i} {j} {k} m Q
  K     : ⊢⟪_⟫_ {j} {k} m Q
  U     : ⊢⟦_⟧ᵀ_ {i} {j} {k} m Q
  I     : ⊢⟪_⟫ᵀ_ {j} {k} m Q -}

⟦wk⟧ : {m : Mode (q , i , j , 1 , o)} {n : Mode (q′ , i′ , j′ , k′ , 1)} → 
  ⟦ m ⟧ → ⟦ n ⟧ → ⟦ m ⟧

wk : ∀ {m : Mode (q , i , j , 1 , o)} {n : Mode (q′ , i′ , j′ , k′ , 1)} {Q} → 
  Tm m Q → (R : ⟦ n ⟧) → Tm m (⟦wk⟧ Q R)
data Tm where
  
  _▷_ : ∀ {m : Mode (q , i , j , k , 1)} {Q} →
    Tm cx Q →
    ⟦ m ⟧ → 
    Tm cx Q

⟦wk⟧ {m = ty x} Γ r       = Γ ▷ r
⟦wk⟧ {m = ex x} (Γ , t) r = Γ ▷ r , wk t r
⟦wk⟧ {m = su x} (Γ , Δ) r = Γ ▷ r , Δ

{-
data _⊑_ : ℕ → ℕ → Set where
  rfl  : s ⊑ s
  v⊑t  : V ⊑ T

_⊔_ : ℕ → ℕ → ℕ
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
record Suc (q : ℕ) : Set where
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
  -- the seCxd uses the first clause.. 
  V<T {T} = record { wk = λ x _ → x [ id ⁺ _ ] } 

-- [MW] syntax 
suc[_] : ∀ q → Γ ⊢[ q ] B → ∀ A → Γ ▷ A ⊢[ q ] B
suc[_] _ = wk

_∘_ : Γ ⊩[ q ] Θ → Δ ⊩[ r ] Γ → Δ ⊩[ q ⊔ r ] Θ
ε ∘ ys         = ε
(xs , x) ∘ ys  = (xs ∘ ys) , x [ ys ]
 -}