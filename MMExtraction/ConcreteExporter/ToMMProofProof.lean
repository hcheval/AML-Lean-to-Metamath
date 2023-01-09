import MatchingLogic 
import MMExtraction.MMBuilder
import MMExtraction.ConcreteExporter.ToMMClaim
import MMExtraction.ConcreteExporter.ToMMProof 
import MMExtraction.ConcreteExporter.Shape 
import MMExtraction.ConcreteExporter.Var
-- import MMExtraction.ConcreteExporter.Freshness 
-- import MMExtraction.ConcreteExporter.Positivity 
import MMExtraction.ConcreteExporter.ToLabel 
import MMExtraction.ConcreteExporter.MLITP

set_option autoImplicit false 
set_option linter.unusedVariables.patternVars false

namespace ML 

open ML.Meta
open MLITP (Statement)


variable {𝕊 : Type} [DecidableEq 𝕊] [ToMMClaim 𝕊]

def Proof.statements {Γ : Premises 𝕊} {φ : Pattern 𝕊} (proof : Proof Γ φ)
  (matchings : List <| Shape 𝕊 := [])
  : List <| Statement 𝕊 := 
  if matchings.find? (fun matching => matching φ |>.isSome) |>.isSome
    then []
  else match proof with 
  | @tautology _ _ φ _ => 
    [.tautology φ]
  | @premise _ _ φ _ hmem => 
    []
  | @modusPonens _ _ φ ψ h₁ h₂ => 
    .union h₁.statements h₂.statements
  | @existQuan _ _ φ x y sfi => 
    [.substitution (.inl x) (.evar y) φ]
  | @existGen _ _ φ ψ x nfv h => 
    h.statements.insert <| .fresh (.inl x) ψ 
  | @existence _ _ x => 
    []
  | @propagationBottomLeft _ _ c => 
    []
  | @propagationBottomRight _ _ c => 
    []
  | @propagationDisjLeft _ _ φ ψ c => 
    [] 
  | @propagationDisjRight _ _ φ ψ c => 
    [] 
  | @propagationExistLeft _ _ φ x c nfv => 
    []
  | @propagationExistRight _ _ φ x c nfv => 
    []
  | @framingLeft _ _ φ ψ χ h => 
    [] 
  | @framingRight _ _ φ ψ χ h => 
    []
  | @substitution _ _ φ ψ X sfi h => 
    h.statements.insert <| .substitution (.inr X) ψ φ
  | @prefixpoint _ _ φ X pos sfi => 
    [.positive (.inr X) φ]
  | @knasterTarski _ _ φ ψ X sfi h => 
    h.statements
  | @Proof.singleton _ _ C₁ C₂ x φ => 
    []

protected def Proof.toMMProof {Γ : Premises 𝕊} {φ : Pattern 𝕊} (proof : Proof Γ φ)
  (shapes : List <| Shape 𝕊 := [])
  (premiseShapes : List <| Shape 𝕊 := [])
  : Option MMProof := 
do 
  for matching in shapes do 
    if let some ⟨parts, label⟩ := matching φ then 
      return .app label <| parts.map fun ⟨_, _, part⟩ => toMMProof part 
  match proof with 
  | @tautology _ _ φ _ => 
    return .app (MLITP.Statement.tautology φ |>.toLabel) []
  | @premise _ _ φ _ hmem => 
    let mut result : Option MMProof := none 
    for matching in premiseShapes do 
      if let some ⟨parts, label⟩ := matching φ then 
        result := some <| .app label <| parts.map fun ⟨_, _, part⟩ => toMMProof part 
        break
    result
  | @modusPonens _ _ φ ψ h₁ h₂ => 
    return .app "proof-rule-mp" [
      φ.toMMProof, 
      ψ.toMMProof, 
      ← h₂.toMMProof, 
      ← h₁.toMMProof 
    ] 
  | @existQuan _ _ φ x y sfi => 
    return .app "proof-rule-exists" [
      φ[x ⇐ᵉ y].toMMProof, 
      φ.toMMProof, 
      x.toMMProof, 
      y.toMMProof, 
      .app (MLITP.Statement.substitution (.inl x) (.evar y) φ |>.toLabel) []  
    ]
  | @existGen _ _ φ ψ x nfv h => 
    return .app "proof-rule-gen" [
      φ.toMMProof, 
      ψ.toMMProof, 
      x.toMMProof, 
      .app (MLITP.Statement.fresh (.inl x) ψ |>.toLabel) [], 
      ← h.toMMProof
    ]
  | @existence _ _ x => 
    return .app "proof-rule-existence" [x.toMMProof]
  | @propagationBottomLeft _ _ c => 
    return .app "proof-rule-propagation-bot" [
    -- add fresh #Pattern c and fresh #Variable xX together with the essential that ph' is a context in xX and that c the pattern is the substitution of bot in the context
  ]
  | @propagationBottomRight _ _ c => 
    return .app "not-implemented" []
  | @propagationDisjLeft _ _ φ ψ c => 
    return .app "not-implemented" [] 
  | @propagationDisjRight _ _ φ ψ c => 
    return .app "not-implemented" [] 
  | @propagationExistLeft _ _ φ x c nfv => 
    return .app "not-implemented" []
  | @propagationExistRight _ _ φ x c nfv => 
    return .app "not-implemented" []
  | @framingLeft _ _ φ ψ χ h => 
    return .app "not-implemented" [] 
  | @framingRight _ _ φ ψ χ h => 
    return .app "not-implemented" []
  | @substitution _ _ φ ψ X sfi h => 
    return .app "proof-rule-set-var-substitution" [
      φ.toMMProof, 
      ψ.toMMProof, 
      X.toMMProof, 
      .app (MLITP.Statement.substitution (.inr X) ψ φ |>.toLabel) [],
      ← h.toMMProof
    ]
  | @prefixpoint _ _ φ X pos sfi => 
    return .app "proof-rule-prefixpoint" [
      φ.toMMProof, 
      X.toMMProof /- here to insert `sfi`-/, 
      .app (MLITP.Statement.positive (.inr X) φ |>.toLabel) []
    ]
  | @knasterTarski _ _ φ ψ X sfi h => 
    return .app "proof-rule-kt" [
      φ.toMMProof, 
      ψ.toMMProof, 
      X.toMMProof /- here to insert `sfi`-/, 
      ← h.toMMProof
    ]
  | @Proof.singleton _ _ C₁ C₂ x φ => 
    return .app "proof-rule-singleton" [/- here to insert C₁ C₂ as proofs-/ x.toMMProof, φ.toMMProof]

-- instance {Γ : Premises 𝕊} {φ : Pattern 𝕊} : ToMMProof <| Proof Γ φ := ⟨Proof.toMMProof⟩







def thm (φ ψ χ : Pattern Empty) : ∅ ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ (φ ⇒ χ) := Proof.tautology <| by 
  unfold_tautology!
  intros h h' 
  exact h' ∘ h

#eval thm ⊥ ⊤ ⊥ |>.toMMProof 



#eval (@Proof.implSelf Empty ∅ ⊥).toMMProof (matchings := Shape.standardPropositional) |>.get!

#eval (@Proof.weakeningDisj Empty ∅ ⊤ ⊥).toMMProof (matchings := Shape.standardPropositional) |>.get! 

#eval (@Proof.exFalso Empty ∅ ⊥).toMMProof |>.get!

-- ⊥ ⇒ ⊥       ?φ ⇒ ?φ 
-- ⊤ ⇒ ⊤       ?φ ⇒ ?φ


