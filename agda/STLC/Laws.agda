{-# OPTIONS --rewriting #-}
module STLC.Laws where

open import STLC.Definitions


{- tm[] : {x : Γ ⊢[ q ] A}{σ : Γ ⊩[ r ] Θ}
     → tm⊑ (x [ σ ]) ≡ (tm⊑ x) [ σ ]
tm[] {q = V} = refl
tm[] {q = T} = refl

tm⊑zero : (q⊑r : q ⊑ r) → zero[_] {Γ = Γ}{A = A} r ≡ tm⊑ q⊑r zero[ q ]
tm⊑zero rfl = refl
tm⊑zero v⊑t = refl -}

{- zero[]  : zero[ q ] [ σ , x ] ≡ tm⊑ x 
zero[] {q = V} = refl
zero[] {q = T} = refl
 -}

⁺-nat[]v : i [ σ ⁺ A ] ≡ suc[ q ] (i [ σ ]) A
⁺-nat[]v {q = V} = refl
⁺-nat[]v {q = T} = refl

[id] : x [ id[ V ] ] ≡ x
[id] {x = zero}     = refl
[id] {x = suc i A}  = 
   i [ id[ _ ] ⁺ A ]  ≡⟨ ⁺-nat[]v {i = i} ⟩
   suc (i [ id[ _ ] ]) A
   ≡⟨ cong (λ j → suc j A) ([id] {x = i}) ⟩      
   suc i A       ∎
[id] {x = ` i}    =
   cong `_ ([id] {x = i})
[id] {x = t · u}  =
   cong₂ _·_ ([id] {x = t}) ([id] {x = u})
[id] {x = ƛ t}    =
   cong ƛ_ ( [id] {x = t})