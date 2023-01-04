import MatchingLogic 
import MMExtraction.MMBuilder 
import MMExtraction.ConcreteExporter.Var

namespace ML 

open ML.Meta

variable {𝕊 : Type} 




mutual 
  /--
    `Positive xX φ` is an inductive representation of a Metamath proof that 
    `φ` is positive for `xX`. 
  -/
  inductive Positive (xX : Var) : Pattern 𝕊 → Type where 
  | disjoint (φ) : ¬φ.isVar xX → Positive xX φ
  | var (yY : Var) (φ) : Positive xX φ
  | symbol (σ : 𝕊) : Positive xX (.symbol σ)
  | bot : Positive xX ⊥
  | app (φ₁ φ₂ : Pattern 𝕊) : Positive xX φ₁ → Positive xX φ₂ → Positive xX (φ₁ ⬝ φ₂)
  | imp (φ₁ φ₂ : Pattern 𝕊) : Negative xX φ₁ → Positive xX φ₂ → Positive xX (φ₁ ⇒ φ₂)
  | exist (x : EVar) (φ : Pattern 𝕊) : Positive xX φ → Positive xX (∃∃ x φ)
  | mu (X : SVar) (φ : Pattern 𝕊) : Positive xX φ → Positive xX (μ X φ)

  /--
    `Negative xX φ` is an inductive representation of a Metamath proof that 
    `φ` is negative for `xX`. 
  -/
  inductive Negative (xX : Var) : Pattern 𝕊 → Type where 
  | disjoint (φ) : ¬φ.isVar xX → Negative xX φ
  | var (yY : Var) (φ) : xX ≠ yY → Negative xX φ
  | symbol (σ : 𝕊) : Negative xX (.symbol σ)
  | bot : Negative xX ⊥
  | app (φ₁ φ₂ : Pattern 𝕊) : Negative xX φ₁ → Negative xX φ₂ → Negative xX (φ₁ ⬝ φ₂)
  | imp (φ₁ φ₂ : Pattern 𝕊) : Positive xX φ₁ → Negative xX φ₂ → Negative xX (φ₁ ⇒ φ₂)
  | exist (x : EVar) (φ : Pattern 𝕊) : Negative xX φ → Negative xX (∃∃ x φ)
  | mu (X : SVar) (φ : Pattern 𝕊) : Negative xX φ → Negative xX (μ X φ)
end 

mutual /- `autoPositive` `autoNegative`-/
  -- these are not partial, but I don't care about their termination for the time being 
  /--
    `autoPositive xX φ` produces a Metamath proof that `φ` is a positive for `xX` represented 
    through the `Positive` type if that's the case, and `none` otherwise.
  -/
  partial def autoPositive (xX : Var) (φ : Pattern 𝕊) : Option (Positive xX φ) := do 
    if h : ¬φ.isVar xX then 
      return .disjoint φ h
    else match φ with 
    -- | .evar x => return .app "positive-in-var" [toMMProof xX, toMMProof x] 
    | .evar x => return .var (.inl x) (.evar x)
    | .svar X => return .var (.inr X) (.svar X)
    | .symbol σ => return .symbol σ
    | ⊥ => return .bot 
    | φ₁ ⇒ φ₂ => return .imp φ₁ φ₂ (← autoNegative xX φ₁) (← autoPositive xX φ₂)
    | φ₁ ⬝ φ₂ => return .app φ₁ φ₂ (← autoPositive xX φ₁) (← autoPositive xX φ₂)
    | ∃∃ x ψ => return .exist x ψ (← autoPositive xX ψ) 
    | μ X ψ => return .mu X ψ (← autoPositive xX ψ)

  /--
    `autoNegative xX φ` produces a Metamath proof that `φ` is a negative for `xX` represented 
    through the `Negative` type if that's the case, and `none` otherwise.
  -/
  partial def autoNegative (xX : Var) (φ : Pattern 𝕊) : Option (Negative xX φ) := do 
    if h : ¬φ.isVar xX then 
      return .disjoint φ h
    else match φ with 
    | .evar x => 
      if h' : xX ≠ .inl x then 
        return .var (.inl x) (.evar x) h' 
      else none 
    | .svar X => 
      if h' : xX ≠ .inr X then 
        return .var (.inr X) (.svar X) h'
      else none 
    | .symbol σ => return .symbol σ
    | ⊥ => return .bot 
    | φ₁ ⇒ φ₂ => return .imp φ₁ φ₂ (← autoPositive xX φ₁) (← autoNegative xX φ₂)
    | φ₁ ⬝ φ₂ => return .app φ₁ φ₂ (← autoNegative xX φ₁) (← autoNegative xX φ₂)
    | ∃∃ x ψ => return .exist x ψ (← autoNegative xX ψ) 
    | μ X ψ => return .mu X ψ (← autoNegative xX ψ)
end 



-- mutual /- `autoPositive` `autoNegative`-/
--   -- these are not partial, but I don't care about their termination for the time being 
--   partial def autoPositiveDirect (xX : Var) (φ : Pattern 𝕊) : Option MMProof := do 
--     if φ.isVar xX then 
--       return .app "positive-disjoint" [toMMProof xX, toMMProof φ]
--     else match φ with 
--     | .evar x => return .app "positive-in-var" [toMMProof xX, toMMProof x] 
--     | .svar X => return .app "positive-in-var" [toMMProof xX, toMMProof X]
--     | .symbol σ => return .app "positive-in-symbol" [toMMProof xX, toMMProof σ]
--     | ⊥ => return .app "positive-in-bot" [toMMProof xX]
--     | φ₁ ⇒ φ₂ => return .app "positive-in-imp" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, ← autoNegativeDirect xX φ₁, ← autoPositiveDirect xX φ₂]
--     | φ₁ ⬝ φ₂ => return .app "positive-in-app" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, ← autoPositiveDirect xX φ₁, ← autoPositiveDirect xX φ₂] 
--     | ∃∃ x ψ => return .app "positive-in-exists" [toMMProof xX, toMMProof ψ, ← autoPositiveDirect xX ψ]
--     | μ X ψ => return .app "positive-in-mu" [toMMProof xX, toMMProof ψ, ← autoPositiveDirect xX ψ]

--   partial def autoNegativeDirect (xX : Var) (φ : Pattern 𝕊) : Option MMProof := do 
--     if φ.isVar xX then 
--       return .app "negative-disjoint" [toMMProof xX, toMMProof φ]
--     else match φ with 
--     | .evar x => 
--       if xX != .inl x then 
--         return .app "negative-in-var" [toMMProof xX, toMMProof x] 
--       else none -- this I think is needed to match the MM definition, but evars should never be negative, the notion does not exist for them
--     | .svar X => 
--       if xX != .inr X then 
--         return .app "negative-in-var" [toMMProof xX, toMMProof X]
--       else none 
--     | .symbol σ => return .app "negative-in-symbol" [toMMProof xX, toMMProof σ]
--     | ⊥ => return .app "negative-in-bot" [toMMProof xX]
--     | φ₁ ⇒ φ₂ => return .app "negative-in-imp" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, ← autoPositiveDirect xX φ₁, ← autoNegativeDirect xX φ₂]
--     | φ₁ ⬝ φ₂ => return .app "negative-in-app" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, ← autoNegativeDirect xX φ₁, ← autoNegativeDirect xX φ₂] 
--     | ∃∃ x ψ => return .app "negative-in-exists" [toMMProof xX, toMMProof ψ, ← autoNegativeDirect xX ψ]
--     | μ X ψ => return .app "negative-in-mu" [toMMProof xX, toMMProof ψ, ← autoNegativeDirect xX ψ]
-- end 
