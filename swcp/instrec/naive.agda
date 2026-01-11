module naive where

infix   3  _∋_
infix   3  _⊢_
infix   3  _⊩_
infixl  4  _,_
infix   3  _⊩v_
infix   8  _[_] 
infix   8  _[_]v

data Ty : Set where
  o    : Ty
  _⇒_  : Ty → Ty → Ty

data Con : Set where
  •    : Con
  _▷_  : Con → Ty → Con

variable
  A B C : Ty
  Γ Δ Θ : Con  

data _∋_ : Con → Ty → Set where 
  zero  :  Γ ▷ A ∋ A
  suc   :  Γ ∋ A → (B : Ty) 
        →  Γ ▷ B ∋ A

data _⊢_ : Con → Ty → Set where 
  `_   :  Γ ∋ A → Γ ⊢ A
  _·_  :  Γ ⊢ A ⇒ B → Γ ⊢ A →  Γ ⊢ B
  ƛ_   :  Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B  

data _⊩_ : Con → Con → Set where
  ε    : Γ ⊩ •
  _,_  : Γ ⊩ Δ → Γ ⊢ A → Γ ⊩ Δ ▷ A  

_^_ : Γ ⊩ Δ → (A : Ty) → Γ ▷ A ⊩ Δ ▷ A

_v[_] : Γ ∋ A → Δ ⊩ Γ → Δ ⊢ A
zero       v[ ts , t ] = t
(suc i _)  v[ ts , t ] = i v[ ts ]

_[_] : Γ ⊢ A → Δ ⊩ Γ → Δ ⊢ A
(` i)   [ ts ]       =  i v[ ts ]
(t · u) [ ts ]       =  (t [ ts ]) · (u [ ts ])
(ƛ t)   [ ts ]       =  ƛ (t [ ts ^ _ ])

_⁺_ : Γ ⊩ Δ → (A : Ty) → Γ ▷ A ⊩ Δ
ts ^ A = ts ⁺ A , ` zero 

suc-tm : Γ ⊢ B → (A : Ty) → Γ ▷ A ⊢ B

ε         ⁺ A  = ε
(ts , t)  ⁺ A  = ts ⁺ A , suc-tm t A  

data _⊩v_ : Con → Con → Set where
  ε   : Γ ⊩v •
  _,_ : Γ ⊩v Δ → Γ ∋ A → Γ ⊩v Δ ▷ A

_v[_]v : Γ ∋ A → Δ ⊩v Γ → Δ ∋ A
zero       v[ is , i ]v  = i
(suc i _)  v[ is , j ]v  = i v[ is ]v

_⁺v_ : Γ ⊩v Δ → ∀ A → Γ ▷ A ⊩v Δ
ε         ⁺v A           = ε
(is , i)  ⁺v A           = is ⁺v A , suc i A

_^v_ : Γ ⊩v Δ → ∀ A → Γ ▷ A ⊩v Δ ▷ A
is ^v A                  = is ⁺v A , zero 

_[_]v : Γ ⊢ A → Δ ⊩v Γ → Δ ⊢ A
(` i)    [ is ]v  =  ` (i v[ is ]v)
(t · u)  [ is ]v  =  
  (t [ is ]v) · (u [ is ]v)
(ƛ t)    [ is ]v  =  ƛ (t [ is ^v _ ]v)

idv : Γ ⊩v Γ
idv {Γ = •}      = ε
idv {Γ = Γ ▷ A}  = idv ^v A

suc-tm t A       = t [ idv ⁺v A ]v
