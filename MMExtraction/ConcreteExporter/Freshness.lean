import MatchingLogic 
import MMExtraction.MMBuilder 
import MMExtraction.ConcreteExporter.Var

namespace ML 

open ML.Meta

variable {𝕊 : Type} 

/--
  `Fresh xX φ` is an inductive representation of a Metamath proof 
  that `xX` is fresh in `φ`. 
-/
inductive Fresh (xX : Var) : Pattern 𝕊 → Type where 
| var (yY : Var) : xX ≠ yY → Fresh xX yY.toPattern 
| symbol (σ : 𝕊) : Fresh xX (.symbol σ)
| bot : Fresh xX (⊥ : Pattern 𝕊)
| imp (φ ψ : Pattern 𝕊) : Fresh xX φ → Fresh xX ψ → Fresh xX (φ ⇒ ψ)
| app (φ ψ : Pattern 𝕊) : Fresh xX φ → Fresh xX ψ → Fresh xX (φ ⬝ ψ)
| exist (x : EVar) (φ : Pattern 𝕊) : xX ≠ .inl x → Fresh xX φ → Fresh xX (∃∃ x φ)
| existShadowed (x : EVar) (φ : Pattern 𝕊) : xX = .inl x → Fresh xX (∃∃ x φ)
| mu (X : SVar) (φ : Pattern 𝕊) : xX ≠ .inr X → Fresh xX φ → Fresh xX (μ X φ)
| muShadowed (X : SVar) (φ : Pattern 𝕊) : xX = .inr X → Fresh xX (μ X φ)


/--
  `autoFresh xX φ` produces a Metamath proof that `xX` is fresh in `φ` represented  
  through the `Fresh` type if that's the case, and `none` otherwise.
-/
def autoFresh (xX : Var) (φ : Pattern 𝕊) : Option (Fresh xX φ) := do 
  match φ with 
  | .evar x =>
    if h : xX ≠ .inl x then return .var (.inl x) h
    else none 
  | .svar X =>  
    if h : xX ≠ .inr X then return .var (.inr X) h
    else none 
  | .symbol σ => return .symbol σ
  | ⊥ => return .bot 
  | φ₁ ⇒ φ₂ => return .imp φ₁ φ₂ (← autoFresh xX φ₁) (← autoFresh xX φ₂)
  | φ₁ ⬝ φ₂ => return .app φ₁ φ₂ (← autoFresh xX φ₁) (← autoFresh xX φ₂)
  | ∃∃ x ψ => 
    if h : xX ≠ .inl x then 
      return .exist x ψ h (← autoFresh xX ψ)
    else 
      return .existShadowed x ψ (by simp_all)
  | μ X ψ => 
    if h : xX ≠ .inr X then 
      return .mu X ψ h (← autoFresh xX ψ) 
    else 
      return .muShadowed X ψ (by simp_all)

def autoFreshEVar (x : EVar) (φ : Pattern 𝕊) : Option (Fresh (.inl x) φ) := 
  autoFresh (.inl x) φ

def autoFreshSVar (X : SVar) (φ : Pattern 𝕊) : Option (Fresh (.inr X) φ) := 
  autoFresh (.inr X) φ

-- def autoFreshDirect (xX : Var) (φ : Pattern 𝕊) : Option MMProof := do
--   match φ with 
--   | .evar x => 
--     if xX != .inl x then 
--       return .app "fresh-in-var" [toMMProof xX, toMMProof x] 
--     else 
--       none 
--   | .svar X => 
--     if xX != .inr X then 
--       return .app "fresh-in-var" [toMMProof xX, toMMProof X]
--     else 
--       none 
--   | .symbol σ => return .app "fresh-in-symbol" [toMMProof xX, toMMProof σ]
--   | ⊥ => return .app "fresh-in-bot" [toMMProof xX]
--   | φ₁ ⇒ φ₂ => return .app "fresh-in-imp" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, ← autoFreshDirect xX φ₁, ← autoFreshDirect xX φ₂]
--   | φ₁ ⬝ φ₂ => return .app "fresh-in-app" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, ← autoFreshDirect xX φ₁, ← autoFreshDirect xX φ₂]
--   | ∃∃ x ψ => 
--     if xX != .inl x then 
--       return .app "fresh-in-exists" [toMMProof xX, toMMProof ψ, ← autoFreshDirect xX ψ]
--     else 
--       return .app "fresh-in-exists-shadowed" [toMMProof xX, toMMProof ψ]
--   | μ X ψ => 
--     if xX != .inr X then 
--       return .app "fresh-in-mu" [toMMProof xX, toMMProof ψ, ← autoFreshDirect xX ψ]
--     else 
--       return .app "fresh-in-mu-shadowed" [toMMProof xX, toMMProof ψ]


-- def autoFreshDirectEVar : EVar → Pattern 𝕊 → Option MMProof := autoFreshDirect ∘ .inl 

-- def autoFreshDirectSVar : SVar → Pattern 𝕊 → Option MMProof := autoFreshDirect ∘ .inr