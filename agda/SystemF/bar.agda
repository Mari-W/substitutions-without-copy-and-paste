{-# OPTIONS --rewriting --local-confluence-check #-}
module bar where

open import Data.Nat
open import Relation.Binary.PropositionalEquality 

{-# BUILTIN REWRITE _≡_ #-}

interleaved mutual 
  lemma : ∀{n} → n + 0 ≡ n
  lemma {zero} = refl

  {-# REWRITE lemma #-}

  it-works : ∀{n} → n + 0 + 0 ≡ n 
  it-works = refl

  lemma {suc n} = cong suc (lemma {n})