import MatchingLogic 
import MMExtraction.ConcreteExporter.Var 

namespace ML

class ToMMClaim (α : Type) where 
  toMMClaim : α → String 
export ToMMClaim (toMMClaim)

instance : ToMMClaim Empty := ⟨Empty.rec⟩

protected def EVar.toMMClaim : EVar → String 
  | ⟨idx⟩ => s! "_x{idx}"

instance : ToMMClaim EVar := ⟨EVar.toMMClaim⟩

protected def SVar.toMMClaim : SVar → String 
  | ⟨idx⟩ => s! "_X{idx}"

instance : ToMMClaim SVar := ⟨SVar.toMMClaim⟩

protected def Var.toMMClaim : Var → String 
  | .inl x => toMMClaim x 
  | .inr X => toMMClaim X 

instance : ToMMClaim Var := ⟨Var.toMMClaim⟩

section variable {𝕊 : Type} [ToMMClaim 𝕊]

protected def Pattern.toMMClaim : Pattern 𝕊 → String 
  | evar x => x.toMMClaim
  | svar X => X.toMMClaim
  | ⊥ => "\\bot"
  | φ ⇒ ψ => s! "( \\imp {φ.toMMClaim} {ψ.toMMClaim} )"
  | φ ⬝ ψ => s! "( \\app {φ.toMMClaim} {ψ.toMMClaim} )"
  | ∃∃ x φ => s! "( \\exists {x.toMMClaim} {φ.toMMClaim} )"
  | μ X φ => s! "( \\mu {X.toMMClaim} {φ.toMMClaim} )"
  | symbol σ => toMMClaim σ

instance : ToMMClaim <| Pattern 𝕊 := ⟨Pattern.toMMClaim⟩

end 