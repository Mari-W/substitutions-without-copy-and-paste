{-# OPTIONS --rewriting --injective-type-constructors #-}
module init where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

record CwF-simple : Set₁ where
  infix   3  _⊢_
  infix   3  _⊩_
  infixl  4  _▷_
  infixl  4  _,_
  infix   5  _∘_
  infix   5  ƛ_
  infixr  6  _⇒_
  infixl  6  _·_
  infix   8  _[_]
  field
    Con : Set
    _⊩_ : Con → Con → Set

    id : {Γ : Con} → Γ ⊩ Γ
    _∘_ : {Γ Δ Θ : Con}
        → Δ ⊩ Θ → Γ ⊩ Δ → Γ ⊩ Θ
    id∘ : ∀ {Γ Δ}{δ : Γ ⊩ Δ}
       → id ∘ δ ≡ δ
    ∘id : ∀ {Γ Δ}{δ : Γ ⊩ Δ}
       → δ ∘ id ≡ δ
    ∘∘ : ∀ {Γ Δ Θ Ξ}
          {ξ : Θ ⊩ Ξ}{θ : Δ ⊩ Θ}{δ : Γ ⊩ Δ}
          → (ξ ∘ θ) ∘ δ ≡ ξ ∘ (θ ∘ δ)  

    Ty : Set           
    _⊢_ : Con → Ty → Set         
    _[_] : ∀ {Γ Δ A}
        → Γ ⊢ A → Δ ⊩ Γ → Δ ⊢ A
    [id] : ∀ {Γ A}{t : Γ ⊢ A}
        →  (t [ id ]) ≡ t
    [∘] : ∀ {Γ Δ Θ A}
          {t : Θ ⊢ A}{θ : Δ ⊩ Θ}{δ : Γ ⊩ Δ} →
          t [ θ ] [ δ ] ≡ t [ θ ∘ δ ] 

    • : Con
    ε : ∀ {Γ} → Γ ⊩ • 
    •-η : ∀ {Γ}{δ : Γ ⊩ •}
        → δ ≡ ε  

    _▷_ : Con → Ty → Con
    _,_ : ∀ {Γ Δ A}
        → Γ ⊩ Δ → Γ ⊢ A → Γ ⊩ (Δ ▷ A)
    π₀ : ∀ {Γ Δ A}
        → Γ ⊩ (Δ ▷ A) → Γ ⊩ Δ
    π₁ : ∀ {Γ Δ A}
        → Γ ⊩ (Δ ▷ A) → Γ ⊢ A
    ▷-β₀ : ∀ {Γ Δ A}{δ : Γ ⊩ Δ}{t : Γ ⊢ A}
           → π₀ (δ , t) ≡ δ
    ▷-β₁ : ∀ {Γ Δ A}{δ : Γ ⊩ Δ}{t : Γ ⊢ A}
           → π₁ (δ , t) ≡ t
    ▷-η : ∀ {Γ Δ A}{δ : Γ ⊩ (Δ ▷ A)}
           → (π₀ δ , π₁ δ) ≡ δ
    π₀∘ : ∀ {Γ Δ Θ A}{θ : Δ ⊩ (Θ ▷ A)}{δ : Γ ⊩ Δ}
           → π₀ (θ ∘ δ) ≡ π₀ θ ∘ δ
    π₁∘ : ∀ {Γ Δ Θ A}{θ : Δ ⊩ (Θ ▷ A)}{δ : Γ ⊩ Δ}
           → π₁ (θ ∘ δ) ≡ (π₁ θ) [ δ ]  

  _^_ : ∀ {Γ Δ} → Γ ⊩ Δ → ∀ A → Γ ▷ A ⊩ Δ ▷ A
  δ ^ A = (δ ∘ (π₀ id)) , π₁ id

  field
    o : Ty
    _⇒_ : Ty → Ty → Ty
    _·_  : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    ƛ_   : ∀ {Γ A B} → Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B  
    ·[]  : ∀ {Γ Δ A B}
           {t : Γ ⊢ A ⇒ B}{u : Γ ⊢ A}{δ : Δ ⊩ Γ}
           → (t · u) [ δ ] ≡ (t [ δ ]) · (u [ δ ])
    ƛ[] :  ∀ {Γ Δ A B}{t : Γ ▷ A ⊢ B}{δ : Δ ⊩ Γ}
           → (ƛ t) [ δ ] ≡ ƛ (t [ δ ^ _ ])  

open import subst
open import laws
module CwF = CwF-simple

π₀ : Δ ⊩[ q ] (Γ ▷ A) → Δ ⊩[ q ] Γ
π₀ (δ , M) = δ

π₁ : Δ ⊩[ q ] (Γ ▷ A) → Δ ⊢[ q ] A
π₁ (δ , M) = M

tm*⊑ : q ⊑ s → Γ ⊩[ q ] Δ → Γ ⊩[ s ] Δ
tm*⊑ q⊑s ε = ε
tm*⊑ q⊑s (σ , x) = tm*⊑ q⊑s σ , tm⊑ q⊑s x

interleaved mutual
  ⊑∘ : tm*⊑ v⊑t xs ∘ ys ≡ xs ∘ ys
  ∘⊑ : ∀ {xs : Δ ⊩[ T ] Γ} {ys : Θ ⊩[ V ] Δ} → xs ∘ tm*⊑ v⊑t ys ≡ xs ∘ ys
  v[⊑] : i [ tm*⊑ v⊑t ys ] ≡ tm⊑ v⊑t i [ ys ]
  t[⊑] : t [ tm*⊑ v⊑t ys ] ≡ t [ ys ]
  ⊑⁺ : tm*⊑ ⊑t xs ⁺ A ≡ tm*⊑ v⊑t (xs ⁺ A)
  ⊑^ : tm*⊑ v⊑t xs ^ A ≡ tm*⊑ v⊑t (xs ^ A)

  is-cwf : CwF-simple
  is-cwf .CwF.Con = Con

  is-cwf .CwF._⊩_  = _⊩[ T ]_
  is-cwf .CwF.•    = •
  is-cwf .CwF.ε    = ε

  is-cwf .CwF.•-η {δ = ε}  = refl 
  is-cwf .CwF._∘_          = _∘_
  is-cwf .CwF.∘∘           = sym ∘∘

  suc[id⁺] : i [ id ⁺ A ] ≡ suc i A
  suc[id⁺] {i = i} {A = A} =  i [ id ⁺ A ]      ≡⟨ ⁺-nat[]v {i = i} ⟩                       
                              suc (i [ id ]) A  ≡⟨ cong (λ j → suc j A) [id] ⟩
                              suc i A ∎

  ⊑⁺ {xs = ε}      = refl
  ⊑⁺ {xs = xs , x} = cong₂ _,_ ⊑⁺ (cong (`_) suc[id⁺])
  
  ⊑∘ {xs = ε} = refl
  ⊑∘ {xs = xs , x} = cong₂ _,_ ⊑∘ refl

  ∘⊑ {xs = ε} = refl
  ∘⊑ {xs = xs , x} = cong₂ _,_ ∘⊑ (t[⊑] {t = x})

  v[⊑] {i = zero}    {ys = ys , y} = refl
  v[⊑] {i = suc i _} {ys = ys , y} = v[⊑] {i = i}

  ⊑^ = cong₂ _,_ ⊑⁺ refl

  t[⊑] {t = ` i}           = v[⊑] {i = i}
  t[⊑] {t = t · u}         = cong₂ _·_ (t[⊑] {t = t}) (t[⊑] {t = u})
  t[⊑] {t = ƛ t} {ys = ys} =
    ƛ t [ tm*⊑ ⊑t ys ^ _ ]
    ≡⟨ cong (λ ρ → ƛ t [ ρ ]) ⊑^ ⟩
    ƛ t [ tm*⊑ ⊑t (ys ^ _) ] 
    ≡⟨ cong ƛ_ (t[⊑] {t = t}) ⟩
     ƛ t [ ys ^ _ ] ∎

  is-cwf .CwF.id = tm*⊑ v⊑t id

  is-cwf .CwF.id∘ {δ = δ} = 
    tm*⊑ v⊑t id ∘ δ  ≡⟨ ⊑∘ ⟩   
    id ∘ δ           ≡⟨ id∘ ⟩  
    δ ∎

  is-cwf .CwF.∘id {δ = δ} =
    δ ∘ tm*⊑ v⊑t id  ≡⟨ ∘⊑ ⟩   
    δ ∘ id           ≡⟨ ∘id ⟩  
    δ ∎

  is-cwf .CwF.Ty    = Ty
  is-cwf .CwF._⊢_   = _⊢[ T ]_
  is-cwf .CwF._[_]  = _[_]

  is-cwf .CwF.[id] {t = t}  =                   
    t [ tm*⊑ v⊑t id ]  ≡⟨ t[⊑] {t = t} ⟩  
    t [ id ]           ≡⟨ [id] ⟩          
    t                  ∎

  is-cwf .CwF.[∘] {t = t}  = sym ([∘] {x = t})

  is-cwf .CwF._▷_ = _▷_
  is-cwf .CwF._,_ = _,_
  is-cwf .CwF.π₀ = π₀
  is-cwf .CwF.π₁ = π₁
  is-cwf .CwF.▷-β₀ = refl
  is-cwf .CwF.▷-β₁ = refl
  is-cwf .CwF.▷-η {δ = xs , x} = refl
  is-cwf .CwF.π₀∘ {θ = xs , x} = refl
  is-cwf .CwF.π₁∘ {θ = xs , x} = refl

  is-cwf .CwF.o = o
  is-cwf .CwF._⇒_ = _⇒_
  is-cwf .CwF._·_ = _·_
  is-cwf .CwF.ƛ_ = ƛ_
  is-cwf .CwF.·[] = refl

  is-cwf .CwF.ƛ[] {A = A} {t = x} {δ = ys} =  
    ƛ x [ ys ^ A ]                
    ≡⟨ cong (λ ρ → ƛ x [ ρ ^ A ]) (sym ∘id) ⟩         
    ƛ x [ (ys ∘ id) ^ A ]         
    ≡⟨ cong (λ ρ → ƛ x [ ρ , ` zero ]) (sym ⁺-nat∘) ⟩  
    ƛ x [ ys ∘ id ⁺ A , ` zero ]  
    ≡⟨ cong (λ ρ → ƛ x [ ρ , ` zero ]) (sym (∘⊑ {ys = id ⁺ _})) ⟩
    ƛ x [ ys ∘ tm*⊑ v⊑t (id ⁺ A) , ` zero ] ∎

open import Level hiding (suc)

infix 4 _≡[_]≡_

private variable
  ℓ ℓ₁ ℓ₂ : Level

_≡[_]≡_ : ∀ {A B : Set ℓ} → A → A ≡ B → B → Set ℓ
x ≡[ refl ]≡ y = x ≡ y

infix   3  _⊢ᴵ_
infix   3  _⊩ᴵ_
infix   5  _∘ᴵ_
infix   5  ƛᴵ_
infixl  6  _·ᴵ_
infix   8  _[_]ᴵ

postulate
  _⊢ᴵ_ : Con → Ty → Set
  _⊩ᴵ_ : Con → Con → Set

variable
  tᴵ uᴵ vᴵ : Γ ⊢ᴵ A
  δᴵ σᴵ ξᴵ : Δ ⊩ᴵ Γ

postulate
  idᴵ  : Γ ⊩ᴵ Γ
  _∘ᴵ_ : Δ ⊩ᴵ Γ → Θ ⊩ᴵ Δ → Θ ⊩ᴵ Γ
  id∘ᴵ : idᴵ ∘ᴵ δᴵ ≡ δᴵ
  ∘idᴵ : δᴵ ∘ᴵ idᴵ ≡ δᴵ
  ∘∘ᴵ  : (ξᴵ ∘ᴵ σᴵ) ∘ᴵ δᴵ ≡ ξᴵ ∘ᴵ (σᴵ ∘ᴵ δᴵ)

  _[_]ᴵ : Γ ⊢ᴵ A → Δ ⊩ᴵ Γ → Δ ⊢ᴵ A
  [id]ᴵ : tᴵ [ idᴵ ]ᴵ ≡ tᴵ
  [∘]ᴵ  : tᴵ [ σᴵ ]ᴵ [ δᴵ ]ᴵ ≡ tᴵ [ σᴵ ∘ᴵ δᴵ ]ᴵ

  εᴵ   : Δ ⊩ᴵ •
  _,ᴵ_ : Δ ⊩ᴵ Γ → Δ ⊢ᴵ A → Δ ⊩ᴵ (Γ ▷ A)
  π₀ᴵ : Δ ⊩ᴵ Γ ▷ A → Δ ⊩ᴵ Γ
  π₁ᴵ : Δ ⊩ᴵ Γ ▷ A → Δ ⊢ᴵ A

  •-ηᴵ  : δᴵ ≡ εᴵ
  ▷-β₀ᴵ : π₀ᴵ (δᴵ ,ᴵ tᴵ) ≡ δᴵ
  ▷-β₁ᴵ : π₁ᴵ (δᴵ ,ᴵ tᴵ) ≡ tᴵ
  ▷-ηᴵ  : (π₀ᴵ δᴵ ,ᴵ π₁ᴵ δᴵ) ≡ δᴵ
  π₀∘ᴵ  : π₀ᴵ (σᴵ ∘ᴵ δᴵ) ≡ π₀ᴵ σᴵ ∘ᴵ δᴵ
  π₁∘ᴵ  : π₁ᴵ (σᴵ ∘ᴵ δᴵ) ≡ π₁ᴵ σᴵ [ δᴵ ]ᴵ

wkᴵ : Γ ▷ A ⊩ᴵ Γ
wkᴵ = π₀ᴵ idᴵ

zeroᴵ : Γ ▷ A ⊢ᴵ A 
zeroᴵ = π₁ᴵ idᴵ

_^ᴵ_ : Δ ⊩ᴵ Γ → ∀ A → Δ ▷ A ⊩ᴵ Γ ▷ A
δ ^ᴵ A = (δ ∘ᴵ wkᴵ) ,ᴵ zeroᴵ

postulate
  _·ᴵ_ : Γ ⊢ᴵ A ⇒ B → Γ ⊢ᴵ A → Γ ⊢ᴵ B
  ƛᴵ_  : Γ ▷ A ⊢ᴵ B → Γ ⊢ᴵ A ⇒ B
  ·[]ᴵ : (tᴵ ·ᴵ uᴵ) [ δᴵ ]ᴵ ≡ tᴵ [ δᴵ ]ᴵ ·ᴵ uᴵ [ δᴵ ]ᴵ
  ƛ[]ᴵ : (ƛᴵ tᴵ) [ δᴵ ]ᴵ ≡ ƛᴵ (tᴵ [ δᴵ ^ᴵ A ]ᴵ)

sucᴵ : Γ ⊢ᴵ B → ∀ A → Γ ▷ A ⊢ᴵ B
sucᴵ x A = x [ π₀ᴵ idᴵ ]ᴵ

record Motive : Set₁ where
  field
    Conᴹ : Con → Set
    Tyᴹ  : Ty → Set
    Tmᴹ  : Conᴹ Γ → Tyᴹ A → Γ ⊢ᴵ A → Set
    Tmsᴹ : Conᴹ Δ → Conᴹ Γ → Δ ⊩ᴵ Γ → Set

module _ (𝕄 : Motive) where
  open Motive 𝕄

  variable
    Γᴹ Δᴹ θᴹ Ξᴹ : Conᴹ Γ
    Aᴹ Bᴹ Cᴹ Dᴹ : Tyᴹ A
    tᴹ uᴹ vᴹ : Tmᴹ Γᴹ Aᴹ tᴵ
    δᴹ σᴹ ξᴹ : Tmsᴹ Δᴹ Γᴹ δᴵ

  record Methods : Set₁ where
    infixl  4  _▷ᴹ_
    infixl  4  _,ᴹ_
    infix   5  _∘ᴹ_
    infix   5  ƛᴹ_
    infixr  6  _⇒ᴹ_
    infixl  6  _·ᴹ_
    infix   8  _[_]ᴹ
    
    field  
      idᴹ  : Tmsᴹ Γᴹ Γᴹ idᴵ 
      _∘ᴹ_ : Tmsᴹ Δᴹ Γᴹ σᴵ → Tmsᴹ θᴹ Δᴹ δᴵ 
           → Tmsᴹ θᴹ Γᴹ (σᴵ ∘ᴵ δᴵ)
      
      id∘ᴹ : idᴹ ∘ᴹ δᴹ ≡[ cong (Tmsᴹ Δᴹ Γᴹ) id∘ᴵ ]≡ δᴹ
      ∘idᴹ : δᴹ ∘ᴹ idᴹ ≡[ cong (Tmsᴹ Δᴹ Γᴹ) ∘idᴵ ]≡ δᴹ
      ∘∘ᴹ  : (ξᴹ ∘ᴹ σᴹ) ∘ᴹ δᴹ ≡[ cong (Tmsᴹ Ξᴹ Γᴹ) ∘∘ᴵ ]≡ ξᴹ ∘ᴹ (σᴹ ∘ᴹ δᴹ) 

      _[_]ᴹ : Tmᴹ Γᴹ Aᴹ tᴵ → Tmsᴹ Δᴹ Γᴹ δᴵ → Tmᴹ Δᴹ Aᴹ (tᴵ [ δᴵ ]ᴵ)
      
      [id]ᴹ : tᴹ [ idᴹ ]ᴹ ≡[ cong (Tmᴹ Γᴹ Aᴹ) [id]ᴵ ]≡ tᴹ
      [∘]ᴹ  : tᴹ [ σᴹ ]ᴹ [ δᴹ ]ᴹ ≡[ cong (Tmᴹ θᴹ Aᴹ) [∘]ᴵ ]≡ tᴹ [ σᴹ ∘ᴹ δᴹ ]ᴹ

      •ᴹ : Conᴹ •
      εᴹ : Tmsᴹ Δᴹ •ᴹ εᴵ

      •-ηᴹ : δᴹ ≡[ cong (Tmsᴹ Δᴹ •ᴹ) •-ηᴵ ]≡ εᴹ

      _▷ᴹ_ : Conᴹ Γ → Tyᴹ A → Conᴹ (Γ ▷ A)
      _,ᴹ_ : Tmsᴹ Δᴹ Γᴹ δᴵ → Tmᴹ Δᴹ Aᴹ tᴵ → Tmsᴹ Δᴹ (Γᴹ ▷ᴹ Aᴹ) (δᴵ ,ᴵ tᴵ)
      π₀ᴹ  : Tmsᴹ Δᴹ (Γᴹ ▷ᴹ Aᴹ) δᴵ → Tmsᴹ Δᴹ Γᴹ (π₀ᴵ δᴵ)
      π₁ᴹ  : Tmsᴹ Δᴹ (Γᴹ ▷ᴹ Aᴹ) δᴵ → Tmᴹ Δᴹ Aᴹ (π₁ᴵ δᴵ)

      ▷-β₀ᴹ : π₀ᴹ (δᴹ ,ᴹ tᴹ) ≡[ cong (Tmsᴹ Δᴹ Γᴹ) ▷-β₀ᴵ ]≡ δᴹ
      ▷-β₁ᴹ : π₁ᴹ (δᴹ ,ᴹ tᴹ) ≡[ cong (Tmᴹ Δᴹ Aᴹ) ▷-β₁ᴵ ]≡ tᴹ
      ▷-ηᴹ  : (π₀ᴹ δᴹ ,ᴹ π₁ᴹ δᴹ) ≡[ cong (Tmsᴹ Δᴹ (Γᴹ ▷ᴹ Aᴹ)) ▷-ηᴵ ]≡ δᴹ
      π₀∘ᴹ  : π₀ᴹ (σᴹ ∘ᴹ δᴹ) ≡[ cong (Tmsᴹ θᴹ Γᴹ) π₀∘ᴵ ]≡ π₀ᴹ σᴹ ∘ᴹ δᴹ
      π₁∘ᴹ  : π₁ᴹ (σᴹ ∘ᴹ δᴹ) ≡[ cong (Tmᴹ θᴹ Aᴹ) π₁∘ᴵ ]≡ π₁ᴹ σᴹ [ δᴹ ]ᴹ
    
    wkᴹ : Tmsᴹ (Γᴹ ▷ᴹ Aᴹ) Γᴹ wkᴵ
    wkᴹ = π₀ᴹ idᴹ

    zeroᴹ : Tmᴹ (Γᴹ ▷ᴹ Aᴹ) Aᴹ zeroᴵ
    zeroᴹ = π₁ᴹ idᴹ

    _^ᴹ_ : Tmsᴹ Δᴹ Γᴹ δᴵ → ∀ Aᴹ → Tmsᴹ (Δᴹ ▷ᴹ Aᴹ) (Γᴹ ▷ᴹ Aᴹ) (δᴵ ^ᴵ A)
    δᴹ ^ᴹ Aᴹ = (δᴹ ∘ᴹ wkᴹ) ,ᴹ zeroᴹ

    field
      oᴹ   : Tyᴹ o
      _⇒ᴹ_ : Tyᴹ A → Tyᴹ B → Tyᴹ (A ⇒ B)
      
      _·ᴹ_ : Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ) tᴵ → Tmᴹ Γᴹ Aᴹ uᴵ → Tmᴹ Γᴹ Bᴹ (tᴵ ·ᴵ uᴵ)
      ƛᴹ_  : Tmᴹ (Γᴹ ▷ᴹ Aᴹ) Bᴹ tᴵ → Tmᴹ Γᴹ (Aᴹ ⇒ᴹ Bᴹ) (ƛᴵ tᴵ)
      
      ·[]ᴹ : (tᴹ ·ᴹ uᴹ) [ δᴹ ]ᴹ 
          ≡[ cong (Tmᴹ Δᴹ Bᴹ) ·[]ᴵ 
          ]≡ tᴹ [ δᴹ ]ᴹ ·ᴹ uᴹ [ δᴹ ]ᴹ
      ƛ[]ᴹ : (ƛᴹ tᴹ) [ δᴹ ]ᴹ 
          ≡[ cong (Tmᴹ Δᴹ (Aᴹ ⇒ᴹ Bᴹ)) ƛ[]ᴵ 
          ]≡ ƛᴹ (tᴹ [ δᴹ ^ᴹ Aᴹ ]ᴹ)  

module Eliminator {𝕄} (𝕞 : Methods 𝕄) where
  open Motive 𝕄
  open Methods 𝕞

  elim-con : ∀ Γ → Conᴹ Γ
  elim-ty  : ∀ A → Tyᴹ  A

  elim-con • = •ᴹ
  elim-con (Γ ▷ A) = (elim-con Γ) ▷ᴹ (elim-ty A)

  elim-ty o = oᴹ
  elim-ty (A ⇒ B) = (elim-ty A) ⇒ᴹ (elim-ty B) 

  postulate
    elim-cwf  : ∀ tᴵ → Tmᴹ (elim-con Γ) (elim-ty A) tᴵ
    elim-cwf* : ∀ δᴵ → Tmsᴹ (elim-con Δ) (elim-con Γ) δᴵ

    elim-cwf*-idβ : elim-cwf* (idᴵ {Γ}) ≡ idᴹ
    elim-cwf*-∘β  : elim-cwf* (σᴵ ∘ᴵ δᴵ) 
                  ≡ elim-cwf* σᴵ ∘ᴹ elim-cwf* δᴵ
    -- ...

    elim-cwf*-[]β : elim-cwf (tᴵ [ δᴵ ]ᴵ) 
                  ≡ elim-cwf tᴵ [ elim-cwf* δᴵ ]ᴹ

    elim-cwf*-εβ  : elim-cwf* (εᴵ {Δ = Δ}) ≡ εᴹ
    elim-cwf*-,β  : elim-cwf* (δᴵ ,ᴵ tᴵ) 
                  ≡ (elim-cwf* δᴵ ,ᴹ elim-cwf tᴵ)
    elim-cwf*-π₀β : elim-cwf* (π₀ᴵ δᴵ) 
                  ≡ π₀ᴹ (elim-cwf* δᴵ)
    elim-cwf-π₁β : elim-cwf (π₁ᴵ δᴵ) 
                  ≡ π₁ᴹ (elim-cwf* δᴵ)

    elim-cwf-·β : elim-cwf (tᴵ ·ᴵ uᴵ) 
                ≡ elim-cwf tᴵ ·ᴹ elim-cwf uᴵ
    elim-cwf-ƛβ : elim-cwf (ƛᴵ tᴵ) ≡ ƛᴹ elim-cwf tᴵ

  {-# REWRITE elim-cwf*-idβ elim-cwf*-∘β elim-cwf*-[]β elim-cwf*-εβ elim-cwf*-,β 
              elim-cwf*-π₀β elim-cwf-π₁β elim-cwf-·β elim-cwf-ƛβ #-}

open Motive public
open Methods public
open Eliminator public

cong-const : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {x : A} 
               {y z : B} {p : y ≡ z} 
           → cong (λ _ → x) p ≡ refl
cong-const {p = refl} = refl

{-# REWRITE cong-const #-}

module Recursor (cwf : CwF-simple) where
  cwf-to-motive : Motive
  cwf-to-methods : Methods cwf-to-motive

  rec-con  = elim-con  cwf-to-methods
  rec-ty   = elim-ty   cwf-to-methods
  rec-cwf  = elim-cwf  cwf-to-methods
  rec-cwf* = elim-cwf* cwf-to-methods

  cwf-to-motive .Conᴹ _     = cwf .CwF.Con
  cwf-to-motive .Tyᴹ  _     = cwf .CwF.Ty
  cwf-to-motive .Tmᴹ Γ A _  = cwf .CwF._⊢_ Γ A
  cwf-to-motive .Tmsᴹ Δ Γ _ = cwf .CwF._⊩_ Δ Γ
  
  cwf-to-methods .idᴹ   = cwf .CwF.id
  cwf-to-methods ._∘ᴹ_  = cwf .CwF._∘_
  cwf-to-methods .id∘ᴹ  = cwf .CwF.id∘
  -- ...

  cwf-to-methods .∘idᴹ  = cwf .CwF.∘id
  cwf-to-methods .∘∘ᴹ   = cwf .CwF.∘∘
  cwf-to-methods ._[_]ᴹ = cwf .CwF._[_]
  cwf-to-methods .[id]ᴹ = cwf .CwF.[id]
  cwf-to-methods .[∘]ᴹ  = cwf .CwF.[∘]
  cwf-to-methods .•ᴹ    = cwf .CwF.•
  cwf-to-methods .εᴹ    = cwf .CwF.ε
  cwf-to-methods .•-ηᴹ  = cwf .CwF.•-η
  cwf-to-methods ._▷ᴹ_  = cwf .CwF._▷_
  cwf-to-methods ._,ᴹ_  = cwf .CwF._,_
  cwf-to-methods .π₀ᴹ   = cwf .CwF.π₀
  cwf-to-methods .π₁ᴹ   = cwf .CwF.π₁
  cwf-to-methods .▷-β₀ᴹ = cwf .CwF.▷-β₀
  cwf-to-methods .▷-β₁ᴹ = cwf .CwF.▷-β₁
  cwf-to-methods .▷-ηᴹ  = cwf .CwF.▷-η
  cwf-to-methods .π₀∘ᴹ  = cwf .CwF.π₀∘
  cwf-to-methods .π₁∘ᴹ  = cwf .CwF.π₁∘
  cwf-to-methods .oᴹ    = cwf .CwF.o
  cwf-to-methods ._⇒ᴹ_  = cwf .CwF._⇒_
  cwf-to-methods ._·ᴹ_  = cwf .CwF._·_
  cwf-to-methods .ƛᴹ_   = cwf .CwF.ƛ_
  cwf-to-methods .·[]ᴹ  = cwf .CwF.·[]
  cwf-to-methods .ƛ[]ᴹ  = cwf .CwF.ƛ[]

open Recursor public
{-# INLINE rec-con #-}
{-# INLINE rec-ty #-}

Con≡ : rec-con is-cwf Γ ≡ Γ
Ty≡  : rec-ty  is-cwf A ≡ A

Con≡ {Γ = •} = refl
Con≡ {Γ = Γ ▷ A} = cong₂ _▷_ Con≡ Ty≡

Ty≡ {A = o} = refl
Ty≡ {A = A ⇒ B} = cong₂ _⇒_ Ty≡ Ty≡

{-# REWRITE Con≡ Ty≡ #-}

norm : Γ ⊢ᴵ A → Γ ⊢[ T ] A
norm = rec-cwf is-cwf 

norm* : Δ ⊩ᴵ Γ → Δ ⊩[ T ] Γ
norm* = rec-cwf* is-cwf

⌜_⌝   : Γ ⊢[ q ] A → Γ ⊢ᴵ A
⌜_⌝*  : Δ ⊩[ q ] Γ → Δ ⊩ᴵ Γ

⌜ zero ⌝     = zeroᴵ
⌜ suc i B ⌝  = sucᴵ ⌜ i ⌝ B
⌜ ` i ⌝      = ⌜ i ⌝

⌜ t · u ⌝   = ⌜ t ⌝ ·ᴵ ⌜ u ⌝
⌜ ƛ t ⌝     = ƛᴵ ⌜ t ⌝

⌜ ε ⌝*      = εᴵ
⌜ δ , x ⌝*  = ⌜ δ ⌝* ,ᴵ ⌜ x ⌝

stab : norm ⌜ x ⌝ ≡ tm⊑ ⊑t x
stab {x = zero}     = refl
stab {x = suc i B}  =
  norm ⌜ i ⌝ [ tm*⊑ v⊑t (id ⁺ B) ]  ≡⟨ t[⊑] {t = norm ⌜ i ⌝} ⟩
  norm ⌜ i ⌝ [ id ⁺ B ]             ≡⟨ cong (λ j → suc[ _ ] j B) (stab {x = i}) ⟩
  ` i [ id ⁺ B ]                    ≡⟨ cong `_ suc[id⁺] ⟩
  ` suc i B ∎
stab {x = ` i}      = stab {x = i}
stab {x = t · u}    = cong₂ _·_ (stab {x = t}) (stab {x = u})
stab {x = ƛ t}      = cong ƛ_ (stab {x = t})

compl-𝕄 : Motive

compl-𝕄 .Tmᴹ _ _ tᴵ   = ⌜ norm tᴵ ⌝ ≡ tᴵ
compl-𝕄 .Tmsᴹ _ _ δᴵ  = ⌜ norm* δᴵ ⌝* ≡ δᴵ

compl-𝕄 .Conᴹ _  = ⊤
compl-𝕄 .Tyᴹ  _  = ⊤

⌜zero⌝ : ⌜ zero[_] {Γ = Γ} {A = A} q ⌝ ≡ zeroᴵ
⌜zero⌝ {q = V} = refl
⌜zero⌝ {q = T} = refl

⌜π₀⌝ : ∀ {δ : Δ ⊩[ T ] (Γ ▷ A)}
     → ⌜ π₀ δ ⌝* ≡ π₀ᴵ ⌜ δ ⌝*
⌜π₀⌝ {δ = δ , x} = sym ▷-β₀ᴵ

⌜π₁⌝ : ∀ {δ : Δ ⊩[ T ] (Γ ▷ A)}
     → ⌜ π₁ δ ⌝ ≡ π₁ᴵ ⌜ δ ⌝*
⌜π₁⌝ {δ = δ , x} = sym ▷-β₁ᴵ

⌜[]⌝   : ⌜ x [ ys ] ⌝ ≡ ⌜ x ⌝ [ ⌜ ys ⌝* ]ᴵ
⌜^⌝    : ∀ {xs : Δ ⊩[ q ] Γ} → ⌜ xs ^ A ⌝* ≡ ⌜ xs ⌝* ^ᴵ A
⌜⁺⌝    : ⌜ xs ⁺ A ⌝* ≡ ⌜ xs ⌝* ∘ᴵ wkᴵ
⌜id⌝   : ⌜ id {Γ = Γ} ⌝* ≡ idᴵ
⌜suc⌝  : ⌜ suc[ q ] x B ⌝ ≡ ⌜ x ⌝ [ wkᴵ ]ᴵ

⌜id⌝′ : Sort → ⌜ id {Γ = Γ} ⌝* ≡ idᴵ
⌜id⌝ = ⌜id⌝′ V

{-# INLINE ⌜id⌝ #-}

zero[]ᴵ : zeroᴵ [ δᴵ ,ᴵ tᴵ ]ᴵ ≡ tᴵ
zero[]ᴵ {δᴵ = δᴵ} {tᴵ = tᴵ} =  
  zeroᴵ [ δᴵ ,ᴵ tᴵ ]ᴵ      ≡⟨ sym π₁∘ᴵ ⟩                
  π₁ᴵ (idᴵ ∘ᴵ (δᴵ ,ᴵ tᴵ))  ≡⟨ cong π₁ᴵ id∘ᴵ ⟩ 
  π₁ᴵ (δᴵ ,ᴵ tᴵ)           ≡⟨ ▷-β₁ᴵ ⟩ 
  tᴵ                       ∎

suc[]ᴵ : sucᴵ tᴵ B [ δᴵ ,ᴵ uᴵ ]ᴵ ≡ tᴵ [ δᴵ ]ᴵ
suc[]ᴵ {tᴵ = tᴵ} {B = B} {δᴵ = δᴵ} {uᴵ = uᴵ} =
  sucᴵ tᴵ B [ δᴵ ,ᴵ uᴵ ]ᴵ
  ≡⟨ [∘]ᴵ ⟩
  tᴵ [ wkᴵ ∘ᴵ δᴵ ,ᴵ uᴵ ]ᴵ
  ≡⟨ cong (tᴵ [_]ᴵ) (sym π₀∘ᴵ) ⟩
  tᴵ [ π₀ᴵ (idᴵ ∘ᴵ (δᴵ ,ᴵ uᴵ)) ]ᴵ
  ≡⟨ cong (λ ρ → tᴵ [ π₀ᴵ ρ ]ᴵ) id∘ᴵ ⟩
  tᴵ [ π₀ᴵ (δᴵ ,ᴵ uᴵ) ]ᴵ
  ≡⟨ cong (tᴵ [_]ᴵ) ▷-β₀ᴵ ⟩
  tᴵ [ δᴵ ]ᴵ ∎ 

,∘ᴵ : (δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ ≡ (δᴵ ∘ᴵ σᴵ) ,ᴵ (tᴵ [ σᴵ ]ᴵ)
,∘ᴵ {δᴵ = δᴵ} {tᴵ = tᴵ} {σᴵ = σᴵ} =
  (δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ
  ≡⟨ sym (▷-ηᴵ {δᴵ = (δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ}) ⟩
  π₀ᴵ ((δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ) ,ᴵ π₁ᴵ ((δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ)
  ≡⟨ cong (_,ᴵ π₁ᴵ ((δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ)) π₀∘ᴵ ⟩
  (π₀ᴵ (δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ) ,ᴵ π₁ᴵ ((δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ)
  ≡⟨ cong (λ ρ → (ρ ∘ᴵ σᴵ) ,ᴵ π₁ᴵ ((δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ)) ▷-β₀ᴵ ⟩
  (δᴵ ∘ᴵ σᴵ) ,ᴵ π₁ᴵ ((δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ)
  ≡⟨ cong ((δᴵ ∘ᴵ σᴵ) ,ᴵ_) π₁∘ᴵ ⟩
  (δᴵ ∘ᴵ σᴵ) ,ᴵ (π₁ᴵ (δᴵ ,ᴵ tᴵ) [ σᴵ ]ᴵ)
  ≡⟨ cong (λ ρ → (δᴵ ∘ᴵ σᴵ) ,ᴵ (ρ [ σᴵ ]ᴵ)) ▷-β₁ᴵ ⟩
  (δᴵ ∘ᴵ σᴵ) ,ᴵ (tᴵ [ σᴵ ]ᴵ) ∎

⌜⊑⌝ : ∀ {x : Γ ⊢[ q ] A} → ⌜ tm⊑ ⊑t x ⌝ ≡ ⌜ x ⌝
⌜⊑⌝* : ⌜ tm*⊑ ⊑t xs ⌝* ≡ ⌜ xs ⌝*

⌜⊑⌝ {q = V} = refl
⌜⊑⌝ {q = T} = refl

⌜⊑⌝* {xs = ε} = refl
⌜⊑⌝* {xs = xs , x} = cong₂ _,ᴵ_ ⌜⊑⌝* (⌜⊑⌝ {x = x})

⌜[]⌝ {x = zero} {ys = ys , y} = 
  sym (zero[]ᴵ {δᴵ = ⌜ ys ⌝*})
⌜[]⌝ {x = suc i B} {ys = ys , y} =
  ⌜ i [ ys ] ⌝
  ≡⟨ ⌜[]⌝ {x = i} ⟩
  ⌜ i ⌝ [ ⌜ ys ⌝* ]ᴵ
  ≡⟨ sym suc[]ᴵ ⟩
  sucᴵ ⌜ i ⌝ B [ ⌜ ys ⌝* ,ᴵ ⌜ y ⌝ ]ᴵ ∎
⌜[]⌝ {x = ` i} {ys = ys} = 
  ⌜ tm⊑ ⊑t (i [ ys ]) ⌝
  ≡⟨ ⌜⊑⌝ {x = i [ ys ]} ⟩
  ⌜ i [ ys ] ⌝
  ≡⟨ ⌜[]⌝ {x = i} ⟩
  ⌜ i ⌝ [ ⌜ ys ⌝* ]ᴵ ∎
⌜[]⌝ {x = t · u} {ys = ys} = 
  ⌜ t [ ys ] ⌝ ·ᴵ ⌜ u [ ys ] ⌝
  ≡⟨ cong₂ _·ᴵ_ (⌜[]⌝ {x = t}) (⌜[]⌝ {x = u}) ⟩
  ⌜ t ⌝ [ ⌜ ys ⌝* ]ᴵ ·ᴵ ⌜ u ⌝ [ ⌜ ys ⌝* ]ᴵ
  ≡⟨ sym ·[]ᴵ ⟩
  (⌜ t ⌝ ·ᴵ ⌜ u ⌝) [ ⌜ ys ⌝* ]ᴵ ∎
⌜[]⌝ {x = ƛ t} {ys = ys} = 
  ƛᴵ ⌜ t [ ys ^ _ ] ⌝
  ≡⟨ cong ƛᴵ_ (⌜[]⌝ {x = t}) ⟩
  ƛᴵ ⌜ t ⌝ [ ⌜ ys ^ _ ⌝* ]ᴵ
  ≡⟨ cong (λ ρ → ƛᴵ ⌜ t ⌝ [ ρ ]ᴵ) ⌜^⌝ ⟩
  ƛᴵ ⌜ t ⌝ [ ⌜ ys ⌝* ^ᴵ _ ]ᴵ
  ≡⟨ sym ƛ[]ᴵ ⟩
  (ƛᴵ ⌜ t ⌝) [ ⌜ ys ⌝* ]ᴵ ∎

⌜^⌝ {q = q} = cong₂ _,ᴵ_ ⌜⁺⌝ (⌜zero⌝ {q = q})

⌜⁺⌝ {xs = ε}               = 
  sym •-ηᴵ
⌜⁺⌝ {xs = xs , x} {A = A}  = 
  ⌜ xs ⁺ A ⌝* ,ᴵ ⌜ suc[ _ ] x A ⌝
  ≡⟨ cong₂ _,ᴵ_ ⌜⁺⌝ (⌜suc⌝ {x = x}) ⟩
  (⌜ xs ⌝* ∘ᴵ wkᴵ) ,ᴵ (⌜ x ⌝ [ wkᴵ ]ᴵ)
  ≡⟨ sym ,∘ᴵ ⟩
  (⌜ xs ⌝* ,ᴵ ⌜ x ⌝) ∘ᴵ wkᴵ ∎

⌜id⌝′ {Γ = •}      _ = 
  sym •-ηᴵ
⌜id⌝′ {Γ = Γ ▷ A}  _ = 
  ⌜ id ⁺ A ⌝* ,ᴵ zeroᴵ  ≡⟨ cong (_,ᴵ zeroᴵ) ⌜⁺⌝ ⟩
  ⌜ id ⌝* ^ᴵ A          ≡⟨ cong (_^ᴵ A) ⌜id⌝ ⟩
  idᴵ ^ᴵ A              ≡⟨ cong (_,ᴵ zeroᴵ) id∘ᴵ ⟩
  wkᴵ ,ᴵ zeroᴵ          ≡⟨ ▷-ηᴵ ⟩
  idᴵ                   ∎

⌜suc⌝ {q = V} = refl
⌜suc⌝ {q = T} {x = t} {B = B} =
  ⌜ t [ id ⁺ B ] ⌝
  ≡⟨ ⌜[]⌝ {x = t} ⟩
  ⌜ t ⌝ [ ⌜ id ⁺ B ⌝* ]ᴵ
  ≡⟨ cong (⌜ t ⌝ [_]ᴵ) ⌜⁺⌝ ⟩
  ⌜ t ⌝ [ ⌜ id ⌝* ∘ᴵ wkᴵ ]ᴵ
  ≡⟨ cong (λ ρ → ⌜ t ⌝ [ ρ ∘ᴵ wkᴵ ]ᴵ) ⌜id⌝ ⟩
  ⌜ t ⌝ [ idᴵ ∘ᴵ wkᴵ ]ᴵ
  ≡⟨ cong (⌜ t ⌝ [_]ᴵ) id∘ᴵ ⟩
  ⌜ t ⌝ [ wkᴵ ]ᴵ ∎

⌜∘⌝ : ⌜ xs ∘ ys ⌝* ≡ ⌜ xs ⌝* ∘ᴵ ⌜ ys ⌝*
⌜∘⌝ {xs = ε} = sym •-ηᴵ
⌜∘⌝ {xs = xs , x} {ys = ys} = 
  ⌜ xs ∘ ys ⌝* ,ᴵ ⌜ x [ ys ] ⌝
  ≡⟨ cong₂ _,ᴵ_ ⌜∘⌝ (⌜[]⌝ {x = x}) ⟩
  (⌜ xs ⌝* ∘ᴵ ⌜ ys ⌝*) ,ᴵ (⌜ x ⌝ [ ⌜ ys ⌝* ]ᴵ)
  ≡⟨ sym ,∘ᴵ ⟩
  (⌜ xs ⌝* ,ᴵ ⌜ x ⌝) ∘ᴵ ⌜ ys ⌝* ∎

duip : ∀ {A B : Set ℓ} {x y : A} {z w : B} {p q} {r : (x ≡ y) ≡ (z ≡ w)}
     → p ≡[ r ]≡ q
duip {p = refl} {q = refl} {r = refl} = refl

compl-𝕞 : Methods compl-𝕄

compl-𝕞 .idᴹ = 
  ⌜ tm*⊑ v⊑t id ⌝*  ≡⟨ ⌜⊑⌝* ⟩
  ⌜ id ⌝*           ≡⟨ ⌜id⌝ ⟩
  idᴵ ∎

compl-𝕞 ._∘ᴹ_ {σᴵ = σᴵ} {δᴵ = δᴵ} σᴹ δᴹ = 
  ⌜ norm* σᴵ ∘ norm* δᴵ ⌝*        ≡⟨ ⌜∘⌝ ⟩
  ⌜ norm* σᴵ ⌝* ∘ᴵ ⌜ norm* δᴵ ⌝*  ≡⟨ cong₂ _∘ᴵ_ σᴹ δᴹ ⟩
  σᴵ ∘ᴵ δᴵ ∎

compl-𝕞 ._[_]ᴹ {tᴵ = tᴵ} {δᴵ = δᴵ} tᴹ δᴹ = 
  ⌜ norm tᴵ [ norm* δᴵ ] ⌝
  ≡⟨ ⌜[]⌝ {x = norm tᴵ} ⟩
  ⌜ norm tᴵ ⌝ [ ⌜ norm* δᴵ ⌝* ]ᴵ
  ≡⟨ cong₂ _[_]ᴵ tᴹ δᴹ ⟩
  tᴵ [ δᴵ ]ᴵ ∎
compl-𝕞 .•ᴹ = tt
compl-𝕞 .εᴹ = refl
compl-𝕞 ._▷ᴹ_ _ _ = tt
compl-𝕞 ._,ᴹ_ δᴹ tᴹ = cong₂ _,ᴵ_ δᴹ tᴹ
compl-𝕞 .π₀ᴹ {δᴵ = δᴵ} δᴹ = 
  ⌜ π₀ (norm* δᴵ) ⌝*
  ≡⟨ ⌜π₀⌝ ⟩
  π₀ᴵ ⌜ norm* δᴵ ⌝*
  ≡⟨ cong π₀ᴵ δᴹ ⟩
  π₀ᴵ δᴵ ∎
compl-𝕞 .π₁ᴹ {δᴵ = δᴵ} δᴹ = 
  ⌜ π₁ (norm* δᴵ) ⌝
  ≡⟨ ⌜π₁⌝ ⟩
  π₁ᴵ ⌜ norm* δᴵ ⌝*
  ≡⟨ cong π₁ᴵ δᴹ ⟩
  π₁ᴵ δᴵ ∎
compl-𝕞 .oᴹ = tt
compl-𝕞 ._⇒ᴹ_ _ _ = tt
compl-𝕞 ._·ᴹ_ tᴹ uᴹ = cong₂ _·ᴵ_ tᴹ uᴹ
compl-𝕞 .ƛᴹ_ tᴹ = cong (ƛᴵ_) tᴹ

compl-𝕞 .id∘ᴹ  = duip
compl-𝕞 .∘idᴹ  = duip
compl-𝕞 .∘∘ᴹ   = duip
compl-𝕞 .[id]ᴹ = duip
compl-𝕞 .[∘]ᴹ  = duip
compl-𝕞 .•-ηᴹ  = duip
compl-𝕞 .▷-β₀ᴹ = duip
compl-𝕞 .▷-β₁ᴹ = duip
compl-𝕞 .▷-ηᴹ  = duip
compl-𝕞 .π₀∘ᴹ  = duip
compl-𝕞 .π₁∘ᴹ  = duip
compl-𝕞 .·[]ᴹ  = duip
compl-𝕞 .ƛ[]ᴹ  = duip

compl : ⌜ norm tᴵ ⌝ ≡ tᴵ
compl {tᴵ = tᴵ} = elim-cwf compl-𝕞 tᴵ
