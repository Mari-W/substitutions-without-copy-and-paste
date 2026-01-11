{-# OPTIONS --rewriting --local-confluence-check #-}
module laws where

open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

open import subst public 

tm[] : {x : Θ ⊢[ q ] A}{xs : Γ ⊩[ r ] Θ}
     → tm⊑ ⊑t (x [ xs ]) ≡ (tm⊑ ⊑t x) [ xs ]
tm[] {q = V} = refl
tm[] {q = T} = refl

tm⊑zero : (q⊑r : q ⊑ r) → zero[_] {Γ = Γ}{A = A} r ≡ tm⊑ q⊑r zero[ q ]
tm⊑zero rfl = refl
tm⊑zero v⊑t = refl

zero[]  : zero[ q ] [ xs , x ] ≡ tm⊑ (⊑⊔r {q = q}) x 
zero[] {q = V} = refl
zero[] {q = T} = refl

⁺-nat[]v : i [ xs ⁺ A ] ≡ suc[ q ] (i [ xs ]) A
⁺-nat[]v {i = zero}     {xs = xs , x} = refl
⁺-nat[]v {i = suc j A}  {xs = xs , x} = ⁺-nat[]v {i = j}

[id] : x [ id ] ≡ x
[id] {x = zero}     = refl
[id] {x = suc i A}  = 
   i [ id ⁺ A ]  ≡⟨ ⁺-nat[]v {i = i} ⟩
   suc (i [ id ]) A
   ≡⟨ cong (λ j → suc j A) ([id] {x = i}) ⟩      
   suc i A       ∎
[id] {x = ` i}    =
   cong `_ ([id] {x = i})
[id] {x = t · u}  =
   cong₂ _·_ ([id] {x = t}) ([id] {x = u})
[id] {x = ƛ t}    =
   cong ƛ_ ([id] {x = t})

∘id : xs ∘ id ≡ xs
∘id {xs = ε}       = refl
∘id {xs = xs , x}  = cong₂ _,_ (∘id {xs = xs}) ([id] {x = x})

-- [MW] here the situtation is trickier!
record Suc∘ (q : Sort) (r : Sort) : Set where
   field 
      wk∘ : {x : Γ ⊢[ q ] A} {ys : Δ ⊩[ r ] Γ} → 
         (suc[ _ ] x _) [ ys , y ] ≡ x [ ys ] 
      wk∘₂ : {x : Γ ⊢[ q ] A} {ys : Δ ⊩[ r ] Γ} →
         x [ ys ⁺ B ] ≡ suc[ _ ] (x [ ys ]) B 

open Suc∘ {{...}}

⁺∘ : ∀ {{_ : Suc∘ q r}} 
   {xs : Γ ⊩[ q ] Θ} {ys : Δ ⊩[ r ] Γ} → 
   xs ⁺ A ∘ (ys , x) ≡ xs ∘ ys
⁺∘ {xs = ε}       = refl
⁺∘ {xs = xs , x}  = 
   cong₂ _,_ (⁺∘ {xs = xs}) (wk∘ {x = x})

id∘ : ∀ {{_ : Suc∘ V q}} 
   {xs : Γ ⊩[ q ] Θ}  → 
   id ∘ xs ≡ xs
id∘ {xs = ε}      = refl
id∘ {xs = xs , x} = cong₂ _,_
   (id ⁺ _ ∘ (xs , x)  ≡⟨ ⁺∘ {xs = id} ⟩
   id ∘ xs             ≡⟨ id∘ ⟩
   xs                  ∎)
   refl  

[∘] : ∀ {{_ : Suc∘ q r}} → 
   {xs : Γ ⊩[ q ] Θ} {ys : Δ ⊩[ r ] Γ} → 
   x [ xs ∘ ys ] ≡ x [ xs ] [ ys ]

⁺-nat∘ : ∀ {{_ : Suc∘ q r}} {xs : Γ ⊩[ q ] Θ} {ys : Δ ⊩[ r ] Γ} → 
   xs ∘ (ys ⁺ A) ≡ (xs ∘ ys) ⁺ A
⁺-nat∘ {xs = ε} = refl
⁺-nat∘ {xs = xs , x} =
  cong₂ _,_ (⁺-nat∘ {xs = xs}) (wk∘₂ {x = x})

^∘ :   ∀ {{_ : Suc∘ r s}} {xs : Γ ⊩[ r ] Θ}{ys : Δ ⊩[ s ] Γ}{A : Ty}
      → (xs ∘ ys) ^ A ≡ (xs ^ A) ∘ (ys ^ A)
^∘ {r = r}{s = s}{xs = xs}{ys = ys} {A = A} = 
    (xs ∘ ys) ^ A                  ≡⟨⟩
    (xs ∘ ys) ⁺ A , zero[ r ⊔ s ]  ≡⟨ cong (_, _) (sym (⁺-nat∘ {xs = xs})) ⟩
    xs ∘ (ys ⁺ A) , zero[ r ⊔ s ]                
      ≡⟨ cong₂ _,_ refl (tm⊑zero (⊑⊔r {r = s}{q = r})) ⟩        
    xs ∘ (ys ⁺ A) , tm⊑ (⊑⊔r {q = r}) zero[ s ]  
      ≡⟨ cong₂ _,_ (sym (⁺∘ {xs = xs})) (sym (zero[] {q = r}{x = zero[ s ]}))  ⟩    
    (xs ⁺ A) ∘  (ys ^ A) , zero[ r ] [ ys ^ A ]  ≡⟨⟩  
    (xs ^ A) ∘ (ys ^ A)                          ∎

[∘] {x = zero}     {xs = xs , x}         = refl
[∘] {x = suc i _}  {xs = xs , x}         = [∘] {x = i}
[∘] {x = ` x}      {xs = xs}  {ys = ys}  = 
   tm⊑ ⊑t (x [ xs ∘ ys ])      ≡⟨ cong (tm⊑ ⊑t) ([∘] {x = x}) ⟩
   tm⊑ ⊑t (x [ xs ] [ ys ])    ≡⟨ tm[] {x = x [ xs ]} ⟩        
   (tm⊑ ⊑t (x [ xs ])) [ ys ]  ∎
[∘] {x = t · u}                           = cong₂ _·_ ([∘] {x = t}) ([∘] {x = u})
[∘] {x = ƛ t}      {xs = xs}  {ys = ys}   = cong ƛ_ (
   t [ (xs ∘ ys) ^ _ ]         ≡⟨ cong (λ zs → t [ zs ]) ^∘  ⟩
   t [ (xs ^ _) ∘ (ys ^ _)  ]  ≡⟨ [∘] {x = t} ⟩           
   (t [ xs ^ _ ]) [ ys ^ _ ]   ∎)

module _ where
   private instance
      Vr :  Suc∘ V r
      Vr = record { wk∘ = refl; wk∘₂ = λ {x = i} → ⁺-nat[]v {i = i} }
      Tr : {{_ : Suc∘ r V}} → Suc∘ T r 
      Tr = record 
         { wk∘ = λ {y = y} {x = x} {ys = ys} → 
                 (suc[ T ] x _) [ ys , y ]  ≡⟨⟩
                 x [ id ⁺ _ ] [ ys , y ]    
                 ≡⟨ sym ([∘] {x = x}) ⟩
                 x [ (id ⁺ _) ∘ (ys , y) ]  
                 ≡⟨ cong (λ ρ → x [ ρ ]) ⁺∘  ⟩
                 x [ id ∘ ys  ]             
                 ≡⟨ cong (λ ρ → x [ ρ ]) id∘ ⟩
                 x [ ys ]  ∎
         ; wk∘₂ = λ {B = A} {x = x} {ys = xs} → 
                  x [ xs ⁺ A ]         ≡⟨ cong (λ zs → x [ zs ⁺ A ]) (sym ∘id) ⟩
                  x [ (xs ∘ id) ⁺ A ]  ≡⟨ cong (λ zs → x [ zs ]) (sym (⁺-nat∘ {xs = xs})) ⟩
                  x [ xs ∘ (id ⁺ A) ]  ≡⟨ [∘] {x = x} ⟩
                  x [ xs ] [ id ⁺ A ]  ∎ } 
   VV = Vr 
   VT = Vr
   TV = Tr
   TT = Tr {{Tr}}
   
instance 
   V<T∘ : Suc∘ q r 
   V<T∘ {V} {V} = VV
   V<T∘ {V} {T} = VT
   V<T∘ {T} {V} = TV
   V<T∘ {T} {T} = TT 

∘∘ : xs ∘ (ys ∘ zs) ≡ (xs ∘ ys) ∘ zs
∘∘ {xs = ε} = refl
∘∘ {xs = xs , x} =
   cong₂ _,_ (∘∘ {xs = xs}) ([∘] {x = x})
