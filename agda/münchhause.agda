-- münchhausen method 

data Con : Set
Ty : Con → Set -- forward declaration
data Con where
  · : Con
  _▷_ : (Γ : Con) → Ty Γ → Con

U’ : ∀ {Γ} → Ty Γ -- forward declaration
data Tm : (Γ : Con) → Ty Γ → Set
Ty Γ = Tm Γ U’
data Tm where
  U : ∀ {Γ} → Ty Γ
  Π : ∀ {Γ} → (A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
  lam : ∀ {Γ A B} → Tm (Γ ▷ A) B → Tm Γ (Π A B)
U’ = U

-- stratified
-- ...
