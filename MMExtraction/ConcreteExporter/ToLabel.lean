import MatchingLogic 
import MMExtraction.ConcreteExporter.ToMMClaim

namespace ML 

variable {𝕊 : Type} [ToMMClaim 𝕊]

def Pattern.toLabel (φ : Pattern 𝕊) (labelPrefix := "__") : String :=
  let rec toLabelCore : Pattern 𝕊 → String := 
    fun φ => match φ with 
    | .evar x => s!"{toMMClaim x}" 
    | .svar X => s!"{toMMClaim X}"
    | ⊥ => s!"bot"
    | φ₁ ⇒ φ₂ => s!"LP-{toLabelCore φ₁}-imp-{toLabelCore φ₂}-RP" 
    | φ₁ ⬝ φ₂ => s!"LP-{toLabelCore φ₁}-imp-{toLabelCore φ₂}-RP"
    | ∃∃ x φ₁ => s!"LP-exists-{toMMClaim x}-{toLabelCore φ₁}-RP" 
    | μ X φ₁ => s!"LP-mu-{toMMClaim X}-{toLabelCore φ₁}-RP" 
    | symbol σ => s!"{toMMClaim σ}"
  s!"{labelPrefix}{toLabelCore φ}"


