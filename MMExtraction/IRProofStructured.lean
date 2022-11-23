import Lean 
import MMExtraction.MMBuilder
import MMExtraction.IRPatt
import MatchingLogic

open Lean Elab Term Meta Syntax 

set_option autoImplicit false

namespace ML.Meta

-- we do not yet treat application contexts
inductive IRProof where 
| axK : IRPatt → IRPatt → IRProof 
| axS : IRPatt → IRPatt → IRPatt → IRProof 
| dne : IRPatt → IRProof 
| modusPonens : IRPatt → IRPatt → IRProof → IRProof → IRProof
| existQuan : IRPatt → IRPatt → IRPatt → IRProof → IRProof
| existGen : IRPatt → IRPatt → IRPatt → IRProof → IRProof → IRProof
| existence : IRPatt → IRProof
| substitution : IRPatt → IRPatt → IRPatt → IRProof → IRProof → IRProof
| prefixpoint : IRPatt → IRPatt → IRProof → IRProof → IRProof
| knasterTarski : IRPatt → IRPatt → IRPatt → IRProof → IRProof → IRProof
| hyp (name : String) (assertion : IRPatt) : IRProof
| substitutableHyp (name : String) (type : Expr) : IRProof 
| wrong (msg : String := "") : IRProof


protected def IRProof.toString (prf : IRProof) : String := 
  match prf with 
  | axK φ ψ => s! "[{φ} {ψ} axK]"
  | axS φ ψ χ => s! "[{φ} {ψ} {χ} axS]" 
  | dne φ => s! "[{φ} dne]"
  | modusPonens φ ψ Γφ Γφimpψ => s! "[{φ} {ψ} {Γφ.toString} {Γφimpψ.toString} modus-ponens]{endl}"
  | existQuan φ x y sfi => s! "[{φ} {x} {y} {sfi.toString} exist-quan]{endl}" 
  | existGen φ ψ x nfv Γφimpψ => s! "[{φ} {ψ} {x} {nfv.toString} {Γφimpψ.toString} gen]{endl}"
  | existence x => s! "[{x} existence]{endl}"
  | substitution φ ψ X sfi h => s! "[{φ} {ψ} {X} {sfi.toString} {h.toString} substitution]"
  | knasterTarski φ ψ X sfi h => s! "[{φ} {ψ} {X} {h.toString} {sfi.toString} knaster-tarski]" 
  | prefixpoint φ X hpos sfi => s! "[{φ} {X} {hpos.toString} {sfi.toString} prefixpoint]"
  | hyp id type => s! "({id} : {type}) {endl}"
  | substitutableHyp name type => s! "({name} : {type}) {endl}"
  | wrong msg => s! "(wrong: {msg}) {endl}"

instance : ToString IRProof := ⟨IRProof.toString⟩

def isSubstitutabilityHyp (e : Expr) : Bool := 
  e.isAppOf `ML.Pattern.substitutableForEvarIn

def isFreeEVarHyp (e : Expr) : Bool := 
  e.isAppOf `ML.Pattern.isFreeEvar 


-- would be best with the qq package

partial def proofToIRStructured (e : Expr) (reducing : Bool := true) : MetaM IRProof := do 
  let e ← if reducing then whnf e else pure e 
  if e.isAppOf `ML.Proof.axK then 
    let φ ← patternToIRM e.getAppArgs[2]! 
    let ψ ← patternToIRM e.getAppArgs[3]!
    return .axK φ ψ
  else if e.isAppOf `ML.Proof.axS then 
    let φ ← patternToIRM e.getAppArgs[2]!
    let ψ ← patternToIRM e.getAppArgs[3]!
    let χ ← patternToIRM e.getAppArgs[4]!
    return .axS φ ψ χ
  else if e.isAppOf `ML.Proof.dne then 
    let φ ← patternToIRM e.getAppArgs[2]!
    return .dne φ
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
  else if e.isAppOf `ML.Proof.existence then 
    let x ← patternToIRM e.getAppArgs[2]! 
    return .existence x 
  else if e.isAppOf `ML.Proof.substitution then 
    let φ ← patternToIRM e.getAppArgs[2]!
    let ψ ← patternToIRM e.getAppArgs[3]!
    let X ← patternToIRM e.getAppArgs[4]!
    let sfi ← proofToIRStructured e.getAppArgs[5]!
    let h ← proofToIRStructured e.getAppArgs[6]! 
    return .substitution φ ψ X sfi h 
  else if e.isAppOf `ML.Proof.prefixpoint then 
    let φ ← patternToIRM e.getAppArgs[2]!
    let X ← patternToIRM e.getAppArgs[3]! 
    let hpos ← proofToIRStructured e.getAppArgs[4]! 
    let sfi ← proofToIRStructured e.getAppArgs[5]! 
    return .prefixpoint φ X hpos sfi 
  else if e.isAppOf `ML.Proof.knasterTarski then 
    let φ ← patternToIRM e.getAppArgs[2]!
    let ψ ← patternToIRM e.getAppArgs[3]!
    let X ← patternToIRM e.getAppArgs[4]!
    let sfi ← proofToIRStructured e.getAppArgs[5]!
    let h ← proofToIRStructured e.getAppArgs[6]!
    return .knasterTarski φ ψ X sfi h
  else if e.isMVar then 
    let type ← inferType e
    let name := toString e.mvarId!.name 
    if type.isAppOf `ML.Proof then 
      return .hyp name (← patternToIRM type.getAppArgs[2]!)
    else if isSubstitutabilityHyp type then 
      return .substitutableHyp name type 
    else return .wrong (msg := toString type)
  else if e.isSorry then
    return .wrong "sorry"
  else 
    return .wrong 

namespace IRProof 

def getPatterns (prf : IRProof) : List IRPatt :=
  match prf with 
  | axK φ ψ => [φ, ψ] 
  | axS φ ψ χ => [φ, ψ, χ]
  | dne φ => [φ]
  | modusPonens φ ψ h₁ h₂ => φ :: ψ :: h₁.getPatterns ++ h₂.getPatterns 
  | existQuan φ x y sfi => φ :: x :: y :: sfi.getPatterns
  | existGen φ ψ x nfv Γφimpψ => φ :: ψ :: x :: nfv.getPatterns ++ Γφimpψ.getPatterns
  | existence x => [x]
  | substitution φ ψ X sfi h => φ :: ψ :: X :: sfi.getPatterns ++ h.getPatterns 
  | knasterTarski φ ψ X sfi h => φ :: ψ :: X :: sfi.getPatterns ++ h.getPatterns 
  | prefixpoint φ X hpos sfi => φ :: X :: hpos.getPatterns ++ sfi.getPatterns 
  | hyp id assrt => [assrt]
  | substitutableHyp name type => []
  | wrong msg => []

def getHyps (prf : IRProof) : List (String × IRPatt) := 
  match prf with 
  | axK _ _ => [] 
  | axS _ _ _ => []
  | dne _ => []
  | modusPonens _ _ h₁ h₂ => h₁.getHyps ++ h₂.getHyps 
  | existQuan _ _ _ sfi => sfi.getHyps
  | existGen _ _ _ nfv h => nfv.getHyps ++ h.getHyps
  | existence _ => []
  | substitution _ _ _ sfi h => sfi.getHyps ++ h.getHyps 
  | knasterTarski _ _ _ sfi h => sfi.getHyps ++ h.getHyps 
  | prefixpoint _ _ hpos sfi => hpos.getHyps ++ sfi.getHyps 
  | hyp name assertion => [⟨name, assertion⟩]
  | substitutableHyp name type => []
  | wrong _ => []

def createEnv (proof : IRProof) : Env := 
  let patternsEnv := proof.getPatterns.map IRPatt.createEnv |>.foldl (init := ({} : Env)) (Env.merge)
  let hypEnvs' : List (String × String) := proof.getHyps.map <| fun ⟨name, assertion⟩ => ⟨name, toString assertion⟩
  let hypEnv:= ({} : Env).addEssentials hypEnvs'
  patternsEnv ++ hypEnv


def toMMString (proof : IRProof) : String :=
  match proof with 
  | modusPonens φ ψ hφ hφψ => 
    s! "{φ.toMMPatt.1.toMMInProof} {ψ.toMMPatt.1.toMMInProof} {hφ.toMMString} {hφψ.toMMString} rule-mp"
  | existQuan φ x y sfi => 
    s! "{φ.toMMPatt.1.toMMInProof} {x.toMMPatt.1.toMMInProof} {y.toMMPatt.1.toMMInProof} {sfi.toMMString} proof-rule-gen"
  | hyp name _ => name
  | substitutableHyp name _ => name
  | _ => "toMMString not implemented"
