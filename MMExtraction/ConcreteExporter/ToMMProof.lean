import MatchingLogic 
import MMExtraction.MMBuilder
import MMExtraction.ConcreteExporter.ToMMClaim
import MMExtraction.ConcreteExporter.Var
-- import MMExtraction.ConcreteExporter.Freshness 
-- import MMExtraction.ConcreteExporter.Positivity 
import MMExtraction.ConcreteExporter.ToLabel 

set_option autoImplicit false 
set_option linter.unusedVariables.patternVars false

namespace ML 

open ML.Meta

class ToMMProof (α : Type)  where 
  toMMProof : α → MMProof
export ToMMProof (toMMProof)

instance {𝕊 : Type} [ToMMClaim 𝕊] : ToMMProof 𝕊 where 
  toMMProof σ := .app s!"{toMMClaim σ}-is-symbol" []

protected def EVar.toMMProof : EVar → MMProof 
  | x => .app s! "{x.toMMClaim}-is-element-var" []

instance : ToMMProof EVar where toMMProof := EVar.toMMProof

protected def SVar.toMMProof : SVar → MMProof 
  | X => .app s! "{X.toMMClaim}-is-set-var" []

instance : ToMMProof SVar where toMMProof := SVar.toMMProof

protected def Var.toMMProof : Var → MMProof 
  | .inl x => toMMProof x 
  | .inr X => toMMProof X

instance : ToMMProof Var := ⟨Var.toMMProof⟩

section variable {𝕊 : Type} [ToMMProof 𝕊] 

protected def Pattern.toMMProof : Pattern 𝕊 → MMProof 
| evar x => .app "var-is-pattern" [.app "element-var-is-var" [x.toMMProof]]
| svar X => .app "var-is-pattern" [.app "set-var-is-var" [X.toMMProof]]
| ⊥ => .app "bot-is-pattern" []
| φ ⇒ ψ => .app "imp-is-pattern" [φ.toMMProof, ψ.toMMProof]
| φ ⬝ ψ => .app "app-is-pattern" [φ.toMMProof, ψ.toMMProof]
| ∃∃ x φ => .app "exists-is-pattern" [x.toMMProof, φ.toMMProof] 
| μ X φ => .app "mu-is-pattern" [X.toMMProof, φ.toMMProof]
| symbol σ => .app "symbol-is-pattern" [toMMProof σ]

instance : ToMMProof <| Pattern 𝕊 := ⟨Pattern.toMMProof⟩

-- protected def Fresh.toMMProof {xX : Var} {φ : Pattern 𝕊} (fresh : Fresh xX φ) : MMProof := 
--   match fresh with 
--   | var yY _ => .app "fresh-in-var" [toMMProof xX, toMMProof yY]
--   | symbol σ => .app "fresh-in-symbol" [toMMProof xX, toMMProof σ]
--   | bot => .app "fresh-in-bot" [toMMProof xX, toMMProof (⊥ : Pattern 𝕊)]
--   | imp φ ψ freshφ freshψ => .app "fresh-in-imp" [toMMProof xX, toMMProof φ, toMMProof ψ, freshφ.toMMProof, freshψ.toMMProof]
--   | app φ ψ freshφ freshψ => .app "fresh-in-imp" [toMMProof xX, toMMProof φ, toMMProof ψ, freshφ.toMMProof, freshψ.toMMProof]
--   | exist _ φ _ freshφ => .app "fresh-in-exists" [toMMProof xX, toMMProof φ, freshφ.toMMProof]
--   | existShadowed _ φ _ => .app "fresh-in-exists-shadwoed" [toMMProof xX, toMMProof φ]
--   | mu _ φ _ freshφ => .app "fresh-in-mu" [toMMProof xX, toMMProof φ, freshφ.toMMProof]
--   | muShadowed _ φ _ => .app "fresh-in-mu-shadwoed" [toMMProof xX, toMMProof φ]

-- instance {xX : Var} {φ : Pattern 𝕊} : ToMMProof <| Fresh xX φ where 
--   toMMProof := Fresh.toMMProof

-- mutual
--   protected partial def Positive.toMMProof {xX : Var} {φ : Pattern 𝕊} : Positive xX φ → MMProof 
--     | .disjoint φ _ => .app "positive-disjoint" [toMMProof xX, toMMProof φ]
--     | .var yY φ => .app "positive-in-var" [toMMProof xX, toMMProof yY]
--     | .symbol σ => .app "positive-in-symbol" [toMMProof xX, toMMProof σ]
--     | .bot => .app "positive-in-symbol" [toMMProof xX]
--     | .imp φ₁ φ₂ neg₁ pos₂ => .app "positive-in-imp" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, neg₁.toMMProof, pos₂.toMMProof]
--     | .app φ₁ φ₂ pos₁ pos₂ => .app "positive-in-app" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, pos₁.toMMProof, pos₂.toMMProof]
--     | .exist x φ pos => .app "positive-in-exists" [toMMProof xX, toMMProof φ, pos.toMMProof]
--     | .mu X φ pos => .app "positive-in-mu" [toMMProof xX, toMMProof φ, pos.toMMProof]

--   protected partial def Negative.toMMProof {xX : Var} {φ : Pattern 𝕊} : Negative xX φ → MMProof
--     | .disjoint φ _ => .app "positive-disjoint" [toMMProof xX, toMMProof φ]
--     | .var yY φ _ => .app "positive-in-var" [toMMProof xX, toMMProof yY]
--     | .symbol σ => .app "positive-in-symbol" [toMMProof xX, toMMProof σ]
--     | .bot => .app "positive-in-symbol" [toMMProof xX]
--     | .imp φ₁ φ₂ pos₁ neg₂ => .app "positive-in-imp" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, pos₁.toMMProof, neg₂.toMMProof]
--     | .app φ₁ φ₂ neg₁ neg₂ => .app "positive-in-app" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, neg₁.toMMProof, neg₂.toMMProof]
--     | .exist x φ pos => .app "positive-in-exists" [toMMProof xX, toMMProof x, toMMProof φ, pos.toMMProof]
--     | .mu X φ pos => .app "positive-in-mu" [toMMProof xX, toMMProof X, toMMProof φ, pos.toMMProof] 
-- end 

-- instance {xX : Var} {φ : Pattern 𝕊} : ToMMProof <| Positive xX φ where 
--   toMMProof := Positive.toMMProof 

-- instance {xX : Var} {φ : Pattern 𝕊} : ToMMProof <| Negative xX φ where 
--   toMMProof := Negative.toMMProof 

