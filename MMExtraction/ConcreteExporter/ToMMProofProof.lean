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

@[for_matching_logic, simp]
def Pattern.getFreshSVar : ML.Pattern 𝕊 → SVar 
  | φ => .getFresh φ.svars

def Proof.statements {Γ : Premises 𝕊} {φ : Pattern 𝕊} (proof : Proof Γ φ)
  (shapes : List <| Shape 𝕊 := [])
  : List <| Statement 𝕊 := 
  if shapes.find? (fun shape => shape φ |>.isSome) |>.isSome
    then []
  else match proof with 
  | @tautology _ _ φ _ => 
    [.tautology φ]
  | @premise _ _ φ _ hmem => 
    []
  | @modusPonens _ _ φ ψ h₁ h₂ => 
    .union h₁.statements h₂.statements
  | @existQuan _ _ φ x y sfi => 
    [.substitution (.evar x) (.evar y) φ]
  | @existGen _ _ φ ψ x nfv h => 
    h.statements.insert <| .fresh (.evar x) ψ 
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
    h.statements.insert <| .substitution (.svar X) ψ φ
  | @prefixpoint _ _ φ X pos sfi => 
    [.positive (.svar X) φ]
  | @knasterTarski _ _ φ ψ X sfi h => 
    h.statements
  | @Proof.singleton _ _ C₁ C₂ x φ => 
    []

protected def Proof.toMMProof {Γ : Premises 𝕊} {φ : Pattern 𝕊} (proof : Proof Γ φ)
  (shapes : List <| Shape 𝕊 := Shape.standardPropositional)
  (premiseShapes : List <| Shape 𝕊 := [])
  : Option MMProof := 
do 
  for matching in shapes do 
    if let some ⟨parts, label⟩ := matching φ then 
      return .app label <| parts.map fun ⟨_, _, part⟩ => toMMProof part 
  match proof with 
  | @tautology _ _ φ _ => 
    return .app (Statement.tautology φ |>.toLabel) []
  | @premise _ _ φ _ hmem => 
    let mut result : Option MMProof := none 
    for matching in premiseShapes do 
      if let some ⟨parts, label⟩ := matching φ then 
        result := some <| .app label <| parts.map fun ⟨_, _, part⟩ => toMMProof part 
        break
    result
  | @modusPonens _ _ φ ψ h₁ h₂ => 
    return .app "proof-rule-mp" [
      φ.toMMProof,    -- ph0 
      ψ.toMMProof,    -- ph1 
      ← h₂.toMMProof, -- proof-rule-mp.1
      ← h₁.toMMProof  -- proof-rule-mp.0
    ] 
  | @existQuan _ _ φ x y sfi => 
    return .app "proof-rule-exists" [
      φ[x ⇐ᵉ y].toMMProof,                                             -- ph0
      φ.toMMProof,                                                      -- ph1 
      x.toMMProof,                                                      -- x
      y.toMMProof,                                                      -- y 
      .app (Statement.substitution (.evar x) (.evar y) φ |>.toLabel) [] -- proof-rule-exists.0
    ]
  | @existGen _ _ φ ψ x nfv h => 
    return .app "proof-rule-gen" [
      φ.toMMProof,                                      -- ph0
      ψ.toMMProof,                                      -- ph1
      x.toMMProof,                                      -- x
      ← h.toMMProof,                                    -- proof-rule-gen.0
      .app (Statement.fresh (.evar x) ψ |>.toLabel) []  -- proof-rule.gen.1 
    ]
  | @existence _ _ x => 
    return .app "proof-rule-existence" [
      x.toMMProof -- x 
    ]    
  | @propagationBottomLeft _ _ c => 
    return .app "proof-rule-propagation-bot" [
    -- add fresh #Pattern c and fresh #Variable xX together with the essential that ph' is a context in xX and that c the pattern is the substitution of bot in the context
  ]
  | @propagationBottomRight _ _ c => 
    let X : SVar := c.getFreshSVar 
    return .app "proof-rule-propagation-bot" [
      toMMProof <| X ⬝ c,                                                       -- ph0
      toMMProof <| ⊥ ⬝ c,                                                       -- ph1
      toMMProof <| Var.svar X,                                                  -- xX
      .app (Statement.context (.svar X) (X ⬝ c) |>.toLabel) [],                 -- proof-rule-propagation-bot.0
      .app (Statement.substitution (.svar X) ⊥ (X ⬝ c) (⊥ ⬝ c) |>.toLabel) []   -- proof-rule-propagation-bot.1
    ]
  | @propagationDisjLeft _ _ φ ψ c => 
    return .app "not-implemented" [] 
  | @propagationDisjRight _ _ φ ψ c => 
    let X : SVar := φ ⬝ ψ ⬝ c |>.getFreshSVar 
    return .app "proof-rule-propagation-or" [
      toMMProof <| X ⬝ c,                                                       -- ph0
      toMMProof <| (φ ⋁ ψ) ⬝ c,                                                 -- ph1
      toMMProof <| φ ⬝ c,                                                       -- ph2
      toMMProof <| ψ ⬝ c,                                                       -- ph3     
      toMMProof <| Var.svar X,                                                  -- xX
      .app (Statement.context (.svar X) (X ⬝ c) |>.toLabel) [],                 -- proof-rule-propagation-or.0
      .app (Statement.substitution (.svar X) (φ ⋁ ψ) (X ⬝ c) |>.toLabel) [],    -- proof-rule-propagation-or.1 
      .app (Statement.substitution (.svar X) φ (X ⬝ c) |>.toLabel) [],          -- proof-rule-propagation-or.2
      .app (Statement.substitution (.svar X) ψ (X ⬝ c) |>.toLabel) []           -- proof-rule-propagation-or.3
    ] 
  | @propagationExistLeft _ _ φ x c nfv => 
    return .app "not-implemented" []
  | @propagationExistRight _ _ φ x c nfv => 
    return .app "not-implemented" []
  | @framingLeft _ _ φ ψ χ h => 
    return .app "not-implemented" [] 
  | @framingRight _ _ φ ψ c h => 
    let X := φ ⬝ ψ ⬝ c |>.getFreshSVar 
    let C := c ⬝ X 
    return .app "not-implemented" [
      toMMProof C,                                                     -- ph0
      toMMProof <| C[X ⇐ˢ φ],                                         -- ph1
      toMMProof <| C[X ⇐ˢ ψ],                                         -- ph2
      toMMProof φ,                                                     -- ph3 
      toMMProof ψ,                                                     -- ph4
      toMMProof <| Var.svar X,                                         -- xX 
      .app (Statement.context (.svar X) C |>.toLabel) [],              -- proof-rule-frame.0
      .app (Statement.substitution (.svar X) φ C |>.toLabel) [],       -- proof-rule-frame.1
      .app (Statement.substitution (.svar X) ψ C |>.toLabel) [],       -- proof-rule-frame.2
      ← h.toMMProof                                                    -- proof-rule-frame.3
    ]
  | @substitution _ _ φ ψ X sfi h => 
    return .app "proof-rule-set-var-substitution" [
      φ[X ⇐ˢ ψ].toMMProof,                                              -- ph0
      φ.toMMProof,                                                       -- ph1
      ψ.toMMProof,                                                       -- ph2 
      X.toMMProof,                                                       -- X
      .app (MLITP.Statement.substitution (.svar X) ψ φ |>.toLabel) [],   -- proof-rule-set-var-substitution.0
      ← h.toMMProof                                                      -- proof-rule-set-var-substitution.1
    ]
  | @prefixpoint _ _ φ X pos sfi => 
    return .app "proof-rule-prefixpoint" [
      φ.toMMProof,                                                      
      X.toMMProof /- here to insert `sfi`-/, 
      .app (MLITP.Statement.positive (.svar X) φ |>.toLabel) []
    ]
  | @knasterTarski _ _ φ ψ X sfi h => 
    return .app "proof-rule-kt" [
      φ[X ⇐ˢ ψ].toMMProof,
      φ.toMMProof, 
      ψ.toMMProof, 
      X.toMMProof, 
      .app (Statement.substitution (.svar X) ψ φ |>.toLabel) [],
      ← h.toMMProof
    ]
  | @Proof.singleton _ _ C₁ C₂ x φ => 
    let X : SVar := /- placeholder -/ ⟨101⟩  
    let Y : SVar := /- placeholder -/ ⟨102⟩ 
    return .app "proof-rule-singleton" [
      toMMProof <| C₁.insert X,                                                       -- ph0
      toMMProof <| C₂.insert X,                                                       -- ph1 
      toMMProof φ,                                                                    -- ph2 
      toMMProof <| C₁.insert <| x ⋀ φ,                                                -- ph3
      toMMProof <| C₂.insert <| x ⋀ ∼φ,                                               -- ph4
      toMMProof x,                                                                    -- x
      toMMProof <| Var.svar X,                                                        -- xX
      toMMProof <| Var.svar Y,                                                        -- yY   
      .app (Statement.context (.svar X) (C₁.insert X) |>.toLabel) [],                 -- proof-rule-singleton.0
      .app (Statement.context (.svar Y) (C₂.insert Y) |>.toLabel) [],                 -- proof-rule-singleton.1
      .app (Statement.substitution (.svar X) (x ⋀ φ) (C₁.insert X) |>.toLabel) [],    -- proof-rule-singleton.2
      .app (Statement.substitution (.svar Y) (x ⋀ ∼φ) (C₂.insert Y) |>.toLabel) []    -- proof-rule-singleton.3
    ]

-- instance {Γ : Premises 𝕊} {φ : Pattern 𝕊} : ToMMProof <| Proof Γ φ := ⟨Proof.toMMProof⟩






def thm (φ ψ χ : Pattern Empty) : ∅ ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ (φ ⇒ χ) := Proof.tautology <| by 
  unfold_tautology!
  intros h h' 
  exact h' ∘ h

#eval thm ⊥ ⊤ ⊥ |>.toMMProof 



#eval (@Proof.implSelf Empty ∅ ⊥).toMMProof (shapes := Shape.standardPropositional) |>.get!

#eval (@Proof.weakeningDisj Empty ∅ ⊤ ⊥).toMMProof (shapes := Shape.standardPropositional) |>.get! 

#eval (@Proof.exFalso Empty ∅ ⊥).toMMProof |>.get!

-- ⊥ ⇒ ⊥       ?φ ⇒ ?φ 
-- ⊤ ⇒ ⊤       ?φ ⇒ ?φ


