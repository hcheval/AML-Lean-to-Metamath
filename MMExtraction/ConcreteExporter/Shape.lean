import MatchingLogic 
import MMExtraction.ConcreteExporter.ToMMProof 

namespace ML 

def Shape (𝕊 : Type) := Pattern 𝕊 → Option ((List (Σ (α : Type) (_ : ToMMProof α), α)) × String)

namespace Shape 

variable [DecidableEq 𝕊] [ToMMClaim 𝕊]

def impReflexivity : Shape 𝕊 := 
  fun φ => match φ with 
  | φ₁ ⇒ φ₁' => if φ₁ = φ₁' then return ⟨[⟨_, inferInstance, φ₁⟩], "imp-reflexivity"⟩ else none 
  | _ => none

def impTransitivity : Shape 𝕊 := 
  fun φ => match φ with 
  | (φ₁ ⇒ φ₂) ⇒ (φ₂' ⇒ φ₃) ⇒ (φ₁' ⇒ φ₃') => 
    if φ₁ = φ₁' ∧ φ₂ = φ₂' ∧ φ₃ = φ₃' then 
      some ⟨[⟨_, inferInstance, φ₁⟩, ⟨_, inferInstance, φ₂⟩, ⟨_, inferInstance, φ₃⟩], "imp-transitivity"⟩
    else none 
  | _ => none 

def botElim : Shape 𝕊 := 
  fun φ => match φ with 
  | ⊥ ⇒ φ₁ => some ⟨[⟨_, inferInstance, φ₁⟩], "bot-elim"⟩
  | _ => none 

@[match_pattern, for_matching_logic] def disjunction' := @Pattern.disjunction 

def orIntroLeft : Shape 𝕊 := 
  fun φ => match φ with 
  | φ₁ ⇒ (disjunction' φ₁' φ₂) =>  
    if φ₁ = φ₁' then 
      some ⟨[⟨_, inferInstance, φ₁⟩, ⟨_, inferInstance, φ₂⟩], "or-intro-left-sugar"⟩ 
    else none 
  | _ => none

def standardPropositional : List (Shape 𝕊) := [
  impReflexivity, 
  impTransitivity, 
  botElim, 
  orIntroLeft
]

def axiomDefinedness : Shape Definedness := 
  fun φ => match φ with 
  | .symbol Definedness.defined ⬝ .evar x => some ⟨[⟨_, inferInstance, x⟩], "axiom-definedness"⟩ -- this require for `defined` to be specially exported as `\ceil` 
  | _ => none 



