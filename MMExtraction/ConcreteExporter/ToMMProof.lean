import MatchingLogic 
import MMExtraction.MMBuilder
import MMExtraction.ConcreteExporter.ToMMClaim
import MMExtraction.ConcreteExporter.Var
import MMExtraction.ConcreteExporter.Freshness 
import MMExtraction.ConcreteExporter.Positivity 
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

protected def Fresh.toMMProof {xX : Var} {φ : Pattern 𝕊} (fresh : Fresh xX φ) : MMProof := 
  match fresh with 
  | var yY _ => .app "fresh-in-var" [toMMProof xX, toMMProof yY]
  | symbol σ => .app "fresh-in-symbol" [toMMProof xX, toMMProof σ]
  | bot => .app "fresh-in-bot" [toMMProof xX, toMMProof (⊥ : Pattern 𝕊)]
  | imp φ ψ freshφ freshψ => .app "fresh-in-imp" [toMMProof xX, toMMProof φ, toMMProof ψ, freshφ.toMMProof, freshψ.toMMProof]
  | app φ ψ freshφ freshψ => .app "fresh-in-imp" [toMMProof xX, toMMProof φ, toMMProof ψ, freshφ.toMMProof, freshψ.toMMProof]
  | exist _ φ _ freshφ => .app "fresh-in-exists" [toMMProof xX, toMMProof φ, freshφ.toMMProof]
  | existShadowed _ φ _ => .app "fresh-in-exists-shadwoed" [toMMProof xX, toMMProof φ]
  | mu _ φ _ freshφ => .app "fresh-in-mu" [toMMProof xX, toMMProof φ, freshφ.toMMProof]
  | muShadowed _ φ _ => .app "fresh-in-mu-shadwoed" [toMMProof xX, toMMProof φ]

instance {xX : Var} {φ : Pattern 𝕊} : ToMMProof <| Fresh xX φ where 
  toMMProof := Fresh.toMMProof

mutual
  protected partial def Positive.toMMProof {xX : Var} {φ : Pattern 𝕊} : Positive xX φ → MMProof 
    | .disjoint φ _ => .app "positive-disjoint" [toMMProof xX, toMMProof φ]
    | .var yY φ => .app "positive-in-var" [toMMProof xX, toMMProof yY]
    | .symbol σ => .app "positive-in-symbol" [toMMProof xX, toMMProof σ]
    | .bot => .app "positive-in-symbol" [toMMProof xX]
    | .imp φ₁ φ₂ neg₁ pos₂ => .app "positive-in-imp" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, neg₁.toMMProof, pos₂.toMMProof]
    | .app φ₁ φ₂ pos₁ pos₂ => .app "positive-in-app" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, pos₁.toMMProof, pos₂.toMMProof]
    | .exist x φ pos => .app "positive-in-exists" [toMMProof xX, toMMProof φ, pos.toMMProof]
    | .mu X φ pos => .app "positive-in-mu" [toMMProof xX, toMMProof φ, pos.toMMProof]

  protected partial def Negative.toMMProof {xX : Var} {φ : Pattern 𝕊} : Negative xX φ → MMProof
    | .disjoint φ _ => .app "positive-disjoint" [toMMProof xX, toMMProof φ]
    | .var yY φ _ => .app "positive-in-var" [toMMProof xX, toMMProof yY]
    | .symbol σ => .app "positive-in-symbol" [toMMProof xX, toMMProof σ]
    | .bot => .app "positive-in-symbol" [toMMProof xX]
    | .imp φ₁ φ₂ pos₁ neg₂ => .app "positive-in-imp" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, pos₁.toMMProof, neg₂.toMMProof]
    | .app φ₁ φ₂ neg₁ neg₂ => .app "positive-in-app" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, neg₁.toMMProof, neg₂.toMMProof]
    | .exist x φ pos => .app "positive-in-exists" [toMMProof xX, toMMProof x, toMMProof φ, pos.toMMProof]
    | .mu X φ pos => .app "positive-in-mu" [toMMProof xX, toMMProof X, toMMProof φ, pos.toMMProof] 
end 

instance {xX : Var} {φ : Pattern 𝕊} : ToMMProof <| Positive xX φ where 
  toMMProof := Positive.toMMProof 

instance {xX : Var} {φ : Pattern 𝕊} : ToMMProof <| Negative xX φ where 
  toMMProof := Negative.toMMProof 

-- section Shapes 

--   def Shape (𝕊 : Type) := Pattern 𝕊 → Option ((List (Σ (α : Type) (_ : ToMMProof α), α)) × String)

--   variable [DecidableEq 𝕊]

--   def Shape.impReflexivity : Shape 𝕊 := 
--     fun φ => match φ with 
--     | φ₁ ⇒ φ₂ => if φ₁ = φ₂ then some ⟨[⟨_, inferInstance, φ₁⟩], "imp-reflexivity"⟩ else none 
--     | _ => none

--   def Shape.impTransitivity : Shape 𝕊 := 
--     fun φ => match φ with 
--     | (φ₁ ⇒ φ₂) ⇒ (φ₂' ⇒ φ₃) ⇒ (φ₁' ⇒ φ₃') => 
--       if φ₁ = φ₁' ∧ φ₂ = φ₂' ∧ φ₃ = φ₃' then 
--         some ⟨[⟨_, inferInstance, φ₁⟩, ⟨_, inferInstance, φ₂⟩, ⟨_, inferInstance, φ₃⟩], "imp-transitivity"⟩
--       else none 
--     | _ => none 

--   def Shape.botElim : Shape 𝕊 := 
--     fun φ => match φ with 
--     | ⊥ ⇒ φ₁ => some ⟨[⟨_, inferInstance, φ₁⟩], "bot-elim"⟩
--     | _ => none 

--   set_option trace.compiler.code_gen false
--   @[match_pattern] def disjunction' := @Pattern.disjunction 

--   def Shape.orIntroLeft : Shape 𝕊 := 
--     fun φ => match φ with 
--     | φ₁ ⇒ (disjunction' φ₁' φ₂) =>  
--       if φ₁ = φ₁' then 
--         some ⟨[⟨_, inferInstance, φ₁⟩, ⟨_, inferInstance, φ₂⟩], "or-intro-left-sugar"⟩ 
--       else none 
--     | _ => none

--   def Shape.axiomDefinedness : Shape Definedness := 
--     fun φ => match φ with 
--     | .symbol Definedness.defined ⬝ .evar x => some ⟨[⟨_, inferInstance, x⟩], "axiom-definedness"⟩ -- this require for `defined` to be specially exported as `\ceil` 
--     | _ => none 


--   def Shape.standardPropositional : List (Shape 𝕊) := [impReflexivity, impTransitivity, botElim, orIntroLeft]

-- end Shapes 

-- protected def Proof.toMMProof [DecidableEq 𝕊] [ToMMClaim 𝕊] {Γ : Premises 𝕊} {φ : Pattern 𝕊} (proof : Proof Γ φ)
--   (matchings : List <| Shape 𝕊 := [])
--   (premiseShapes : List <| Shape 𝕊 := [])
--   : Option MMProof := 
-- do 
--   for matching in matchings do 
--     if let some ⟨parts, label⟩ := matching φ then 
--       return .app label <| parts.map fun ⟨_, _, part⟩ => toMMProof part 
--   match proof with 
--   | @tautology _ _ φ _ => 
--     return .app φ.toLabel []
--   | @premise _ _ φ _ hmem => 
--     let mut result : Option MMProof := none 
--     for matching in premiseShapes do 
--       if let some ⟨parts, label⟩ := matching φ then 
--         result := some <| .app label <| parts.map fun ⟨_, _, part⟩ => toMMProof part 
--         break
--     result
--   | @modusPonens _ _ φ ψ h₁ h₂ => 
--     return .app "proof-rule-mp" [φ.toMMProof, ψ.toMMProof, ← h₁.toMMProof, ← h₂.toMMProof] 
--   | @existQuan _ _ φ x y sfi => 
--     return .app "proof-rule-exists" [φ[x ⇐ᵉ y].toMMProof, φ.toMMProof, x.toMMProof, y.toMMProof /- here a proof of substitution -/]
--   | @existGen _ _ φ ψ x nfv h => 
--     return .app "proof-rule-gen" [φ.toMMProof, ψ.toMMProof, x.toMMProof, (← autoFresh (.inl x) ψ).toMMProof, ← h.toMMProof]
--   | @existence _ _ x => 
--     return .app "proof-rule-existence" [x.toMMProof]
--   | @propagationBottomLeft _ _ c => 
--     return .app "proof-rule-propagation-bot" [
--     -- add fresh #Pattern c and fresh #Variable xX together with the essential that ph' is a context in xX and that c the pattern is the substitution of bot in the context
--   ]
--   | @propagationBottomRight _ _ c => 
--     return .app "not-implemented" []
--   | @propagationDisjLeft _ _ φ ψ c => 
--     return .app "not-implemented" [] 
--   | @propagationDisjRight _ _ φ ψ c => 
--     return .app "not-implemented" [] 
--   | @propagationExistLeft _ _ φ x c nfv => 
--     return .app "not-implemented" []
--   | @propagationExistRight _ _ φ x c nfv => 
--     return .app "not-implemented" []
--   | @framingLeft _ _ φ ψ χ h => 
--     return .app "not-implemented" [] 
--   | @framingRight _ _ φ ψ χ h => 
--     return .app "not-implemented" []
--   | @substitution _ _ φ ψ X sfi h => 
--     return .app "proof-rule-set-var-substitution" [φ.toMMProof, ψ.toMMProof, X.toMMProof /- here to insert `sfi`-/ , ← h.toMMProof]
--   | @prefixpoint _ _ φ X pos sfi => 
--     return .app "proof-rule-prefixpoint" [φ.toMMProof, X.toMMProof /- here to insert `sfi`-/ /- pos HACKHACKHACK-/]
--   | @knasterTarski _ _ φ ψ X sfi h => 
--     return .app "proof-rule-kt" [φ.toMMProof, ψ.toMMProof, X.toMMProof /- here to insert `sfi`-/, ← h.toMMProof]
--   | @Proof.singleton _ _ C₁ C₂ x φ => 
--     return .app "proof-rule-singleton" [/- here to insert C₁ C₂ as proofs-/ x.toMMProof, φ.toMMProof]

-- -- instance {Γ : Premises 𝕊} {φ : Pattern 𝕊} : ToMMProof <| Proof Γ φ := ⟨Proof.toMMProof⟩

-- end 







-- def thm (φ ψ χ : Pattern Empty) : ∅ ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ (φ ⇒ χ) := Proof.tautology <| by 
--   unfold_tautology!
--   intros h h' 
--   exact h' ∘ h


-- #eval (@Proof.implSelf Empty ∅ ⊥).toMMProof (matchings := Shape.standardPropositional)

-- #eval (@Proof.weakeningDisj Empty ∅ ⊤ ⊥).toMMProof (matchings := Shape.standardPropositional)

-- #eval (@Proof.exFalso Empty ∅ ⊥).toMMProof 

-- -- ⊥ ⇒ ⊥       ?φ ⇒ ?φ 
-- -- ⊤ ⇒ ⊤       ?φ ⇒ ?φ



-- #check Sum.instMonadSum