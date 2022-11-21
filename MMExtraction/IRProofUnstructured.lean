import Lean 
import MMExtraction.MMBuilder
import MMExtraction.IRPatt
import MatchingLogic

open Lean Elab Term Meta Syntax 

set_option autoImplicit false

namespace ML.Meta

@[reducible] def IRProofToken := IRPatt ⊕ String 
@[reducible] def IRProofUnstructured := List IRProofToken

partial def proofToIRUnstructured (e : Expr) (reducing : Bool := true) : MetaM (IRProofUnstructured × Env) := do 
  let type ← inferType e 
  let ⟨_, _, target⟩ ← forallMetaTelescope type 
  if target.isAppOf `ML.Pattern || target.isAppOf `ML.EVar || target.isAppOf `ML.SVar then 
    let irpatt ← patternToIRM e 
    return ⟨[.inl irpatt], {}⟩
  else 
    let e ← if reducing then whnf e else pure e
    match e with 
    | .app e₁ e₂ => 
      let ⟨prf₁, env₁⟩ ← proofToIRUnstructured e₁ reducing
      let ⟨prf₂, env₂⟩ ← proofToIRUnstructured e₂ reducing
      return ⟨prf₂ ++ prf₁, env₂.merge env₁⟩ 
    | .const id _ => 
      return ⟨[.inr <| toString id], {}⟩
    | .mvar id => 
      let type ← inferType e
      dbg_trace type 
      if type.isAppOf `ML.Proof then 
        -- we create a new essential for it 
        return ⟨[.inr <| toString id.name], ({} : Env).addEssential (toString id.name) (toString type.getAppArgs[2]!)⟩
      else 
        -- we need to also check for substitutability, free-variableness, contextness (maybe)
        return ⟨[], {}⟩
    | _ => return ⟨[], {}⟩

  


  


def IRProofToken.toMMString (token : IRProofToken) : String :=
match token with 
| .inl patt => toString patt.toMMPatt.1 
| .inr name => name

def IRProofUnstructured.toMMProofUnstructured (prf : IRProofUnstructured) : List (MMPatt ⊕ String) :=
  prf.map <| 
    fun token => match token with 
    | .inl patt => .inl patt.toMMPatt.1 
    | .inr name => .inr name

def IRProofUnstructured.toMMStrings (prf : IRProofUnstructured) : List String :=
  prf.map IRProofToken.toMMString