import Lean 
import MMExtraction.MMBuilder
import MMExtraction.IRPatt
import MatchingLogic

open Lean Elab Term Meta Syntax 

set_option autoImplicit false

namespace ML.Meta


inductive IRProofStructured where 
| modusPonens : IRPatt → IRPatt → IRProofStructured → IRProofStructured → IRProofStructured
| existQuan : IRPatt → IRPatt → IRPatt → IRProofStructured → IRProofStructured
| existGen : IRPatt → IRPatt → IRPatt → IRProofStructured → IRProofStructured → IRProofStructured
| existence : IRPatt → IRProofStructured
| substitution : IRPatt → IRPatt → IRPatt → IRProofStructured → IRProofStructured → IRProofStructured
| prefixpoint : IRPatt → IRPatt → IRProofStructured → IRProofStructured → IRProofStructured
| knasterTarski : IRPatt → IRPatt → IRPatt → IRProofStructured → IRProofStructured → IRProofStructured
| tautology : IRPatt → IRProofStructured
| hyp (name : String) (assertion : IRPatt) : IRProofStructured
| substitutableHyp (name : String) (type : Expr) : IRProofStructured 
| wrong (msg : String := "") : IRProofStructured

protected def IRProofStructured.toString (prf : IRProofStructured) : String := 
match prf with 
| modusPonens φ ψ Γφ Γφimpψ => s! "{φ} {ψ} {Γφ.toString} {Γφimpψ.toString} modus-ponens {endl}"
| existQuan φ x y sfi => s! "{φ} {x} {y} {sfi.toString} exist-quan {endl}" 
| existGen φ ψ x nfv Γφimpψ => s! "{φ} {ψ} {x} {nfv.toString} {Γφimpψ.toString} gen {endl}"
| existence x => s! "{x} existence {endl}"
| hyp id type => s! "({id} : {type}) {endl}"
| substitutableHyp name type => s! "({name} : {type}) {endl}"
| tautology φ => s! "{φ} tautology {endl}"
| wrong msg => s! "(wrong: {msg}) {endl}"
| _ => "`ToString` not implemented {endl}"

instance : ToString IRProofStructured := ⟨IRProofStructured.toString⟩

def isSubstitutabilityHyp (e : Expr) : Bool := 
  e.isAppOf `ML.Pattern.substitutableForEvarIn

def isFreeEVarHyp (e : Expr) : Bool := 
  e.isAppOf `ML.Pattern.isFreeEvar 

-- would be best with the qq package

partial def proofToIRStructured (e : Expr) (reducing : Bool := true) : MetaM IRProofStructured := do 
  let e ← if reducing then whnf e else pure e 
  if e.isAppOf `ML.Proof.modusPonens then 
    let φ := e.getAppArgs[2]! 
    let ψ := e.getAppArgs[3]! 
    let Γφ := e.getAppArgs[4]!
    let Γφimpψ := e.getAppArgs[5]! 
    return .modusPonens (← patternToIRM φ) (← patternToIRM ψ) (← proofToIRStructured Γφ reducing) (← proofToIRStructured Γφimpψ reducing)
  else if e.isAppOf `ML.Proof.existQuan then 
    let φ := e.getAppArgs[2]! 
    let x := e.getAppArgs[3]! 
    let y := e.getAppArgs[4]! 
    let sfi := e.getAppArgs[5]! 
    return .existQuan (← patternToIRM φ) (← patternToIRM x) (← patternToIRM y) (← proofToIRStructured sfi) 
  else if e.isAppOf `ML.Proof.existGen then 
    let φ := e.getAppArgs[2]!
    let ψ := e.getAppArgs[3]!
    let x := e.getAppArgs[4]!
    let nfv := e.getAppArgs[5]!
    let Γφimpψ := e.getAppArgs[6]!
    return .existGen (← patternToIRM φ) (← patternToIRM ψ) (← patternToIRM x) (← proofToIRStructured nfv) (← proofToIRStructured Γφimpψ)
  else if e.isAppOf `ML.Proof.tautology then --this case is temporary 
    return .tautology (← patternToIRM e.getAppArgs[2]!)
  else if e.isMVar then 
    let type ← inferType e
    let name := toString e.mvarId!.name 
    if type.isAppOf `ML.Proof then 
      return .hyp name (← patternToIRM type.getAppArgs[2]!)
    else if isSubstitutabilityHyp type then 
      return .substitutableHyp name type 
    else return .wrong (msg := toString type)
  else 
    return .wrong 
