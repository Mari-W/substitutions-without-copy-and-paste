{-# OPTIONS --rewriting --local-confluence-check #-}
module laws where

open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

open import subst public 

[id] : x [ id ] ≡ x

⁺-nat[]v : i [ xs ⁺ A ] ≡ suc[ q ] (i [ xs ]) A
⁺-nat[]v {i = zero}     {xs = xs , x} = refl
⁺-nat[]v {i = suc j A}  {xs = xs , x} = ⁺-nat[]v {i = j}

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

[∘] : x [ xs ∘ ys ] ≡ x [ xs ] [ ys ]

id∘ : id ∘ xs ≡ xs

-- id∘′ : Sort → id ∘ xs ≡ xs
-- id∘ = id∘′ V
-- {-# INLINE id∘ #-}

⁺∘ : xs ⁺ A ∘ (ys , x) ≡ xs ∘ ys

suc[] : (suc[ q ] x _) [ ys , y ] ≡ x [ ys ] 
suc[] {q = V} = refl
suc[] {q = T} {x = x} {ys = ys} {y = y} =
  (suc[ T ] x _) [ ys , y ]  ≡⟨⟩
  x [ id ⁺ _ ] [ ys , y ]    
  ≡⟨ sym ([∘] {x = x}) ⟩
  x [ (id ⁺ _) ∘ (ys , y) ]  
  ≡⟨ cong (λ ρ → x [ ρ ]) ⁺∘  ⟩
  x [ id ∘ ys  ]             
  ≡⟨ cong (λ ρ → x [ ρ ]) id∘ ⟩
  x [ ys ]  ∎

⁺∘ {xs = ε}       = refl
⁺∘ {xs = xs , x}  = 
   cong₂ _,_ (⁺∘ {xs = xs}) (suc[] {x = x})

id∘ {xs = ε}      = refl
id∘ {xs = xs , x} = cong₂ _,_
   (id ⁺ _ ∘ (xs , x)  ≡⟨ ⁺∘ {xs = id} ⟩
   id ∘ xs             ≡⟨ id∘ ⟩
   xs                  ∎)
   refl  


-- id∘′ {xs = ε}       _ = refl
-- id∘′ {xs = xs , x}  _ = cong₂ _,_
--    (id ⁺ _ ∘ (xs , x)  ≡⟨ ⁺∘ {xs = id} ⟩
--    id ∘ xs             ≡⟨ id∘ ⟩
--    xs                  ∎)
--    refl

-- ⁺∘ {xs = ε} = refl
-- ⁺∘ {xs = xs , x} = cong₂ _,_ (⁺∘ {xs = xs}) (suc[] {x = x})

^∘ :  {xs : Γ ⊩[ r ] Θ}{ys : Δ ⊩[ s ] Γ}{A : Ty}
      → (xs ∘ ys) ^ A ≡ (xs ^ A) ∘ (ys ^ A)

tm[] : {x : Θ ⊢[ q ] A}{xs : Γ ⊩[ r ] Θ}
     → tm⊑ ⊑t (x [ xs ]) ≡ (tm⊑ ⊑t x) [ xs ]
tm[] {q = V} = refl
tm[] {q = T} = refl

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

∘∘ : xs ∘ (ys ∘ zs) ≡ (xs ∘ ys) ∘ zs
∘∘ {xs = ε} = refl
∘∘ {xs = xs , x} =
   cong₂ _,_ (∘∘ {xs = xs}) ([∘] {x = x})

⁺-nat∘ : xs ∘ (ys ⁺ A) ≡ (xs ∘ ys) ⁺ A

⁺-nat[] : ∀ {x : Γ ⊢[ q ] B} {xs : Δ ⊩[ r ] Γ} 
        → x [ xs ⁺ A ] ≡ suc[ _ ] (x [ xs ]) A

⁺-nat[] {q = V}{x = i} = ⁺-nat[]v {i = i}

⁺-nat[] {q = T} {A = A} {x = x} {xs = xs} = 
   x [ xs ⁺ A ]         ≡⟨ cong (λ zs → x [ zs ⁺ A ]) (sym ∘id) ⟩
   x [ (xs ∘ id) ⁺ A ]  ≡⟨ cong (λ zs → x [ zs ]) (sym (⁺-nat∘ {xs = xs})) ⟩
   x [ xs ∘ (id ⁺ A) ]  ≡⟨ [∘] {x = x} ⟩
   x [ xs ] [ id ⁺ A ]  ∎

⁺-nat∘ {xs = ε} = refl
⁺-nat∘ {xs = xs , x} =
  cong₂ _,_ (⁺-nat∘ {xs = xs}) (⁺-nat[] {x = x})

tm⊑zero : (q⊑r : q ⊑ r) → zero[_] {Γ = Γ}{A = A} r ≡ tm⊑ q⊑r zero[ q ]
tm⊑zero rfl = refl
tm⊑zero v⊑t = refl

zero[]  : zero[ q ] [ xs , x ] ≡ tm⊑ (⊑⊔r {q = q}) x 
zero[] {q = V} = refl
zero[] {q = T} = refl

^∘ {r = r}{s = s}{xs = xs}{ys = ys} {A = A} = 
    (xs ∘ ys) ^ A                  ≡⟨⟩
    (xs ∘ ys) ⁺ A , zero[ r ⊔ s ]  ≡⟨ cong₂ _,_ (sym (⁺-nat∘ {xs = xs})) refl ⟩
    xs ∘ (ys ⁺ A) , zero[ r ⊔ s ]                
      ≡⟨ cong₂ _,_ refl (tm⊑zero (⊑⊔r {r = s}{q = r})) ⟩        
    xs ∘ (ys ⁺ A) , tm⊑ (⊑⊔r {q = r}) zero[ s ]  
      ≡⟨ cong₂ _,_ (sym (⁺∘ {xs = xs})) (sym (zero[] {q = r}{x = zero[ s ]}))  ⟩    
    (xs ⁺ A) ∘  (ys ^ A) , zero[ r ] [ ys ^ A ]  ≡⟨⟩  
    (xs ^ A) ∘ (ys ^ A)                          ∎
