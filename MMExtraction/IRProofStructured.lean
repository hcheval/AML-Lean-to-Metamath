import Lean 
import MMExtraction.MMBuilder
import MMExtraction.IRPatt
import MMExtraction.Attributes
import MatchingLogic

open Lean Elab Term Meta Syntax 

set_option autoImplicit false

namespace ML.Meta

structure SubstitutabilityHyp where 
  name : String := "" 
  target : IRPatt 
  substituent : IRPatt 
  var : IRPatt 
  deriving Inhabited, Repr, DecidableEq 

def SubstitutabilityHyp.parse (e : Expr) : MetaM (Option SubstitutabilityHyp) := do
  if e.isAppOf `ML.Pattern.substitutableForEvarIn then 
    let var ← patternToIRM e.getAppArgs[1]!
    let target ← patternToIRM e.getAppArgs[2]!
    let substituent ← patternToIRM e.getAppArgs[3]!
    return some { var := var, substituent := substituent, target := target}
  else return none 

structure FreshnessHyp where 
  name : String := ""
  target : IRPatt 
  var : IRPatt 

structure PositivityHyp where 
  name : String := ""
  target : IRPatt 
  var : IRPatt 
  deriving Inhabited, Repr, DecidableEq

def isPositivityHyp (e : Expr) : Bool := 
  e.isAppOf `ML.Pattern.Positive 

def PositivityHyp.parse (e : Expr) : MetaM (Option PositivityHyp) := do 
  if e.isAppOf `ML.Pattern.Positive then 
    let target ← patternToIRM e.getAppArgs[1]!
    let var : IRPatt := .metavar .svar "?who?"
    return some { target := target, var := var}
  else return none 


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
| substitutabilityHyp : SubstitutabilityHyp → IRProof 
| freshnessHyp : FreshnessHyp → IRProof 
| positivityHyp : PositivityHyp → IRProof
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
  | substitutabilityHyp h => s! "({h.name} : {h.var} substitutable for {h.substituent} in {h.target}) {endl}"
  | freshnessHyp h => s! "({h.name} : {h.var} fresh in {h.target})"
  | positivityHyp h => s! "({h.target} positive for {h.name})"
  | wrong msg => s! "(wrong: {msg}) {endl}"

instance : ToString IRProof := ⟨IRProof.toString⟩

def isSubstitutabilityHyp (e : Expr) : Bool := 
  e.isAppOf `ML.Pattern.substitutableForEvarIn

def isFreeEVarHyp (e : Expr) : Bool := 
  e.isAppOf `ML.Pattern.isFreeEvar 

partial def proofToIRStructured (e : Expr) (reducing : Bool := true) : MetaM IRProof := do 
  let e ← if reducing then whnf e else pure e 
  let declName := e.getAppFn.constName! 
  
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
  else if e.isAppOf `ML.Proof.modusPonens then 
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
    if isSubstitutabilityHyp type then 
      let substHyp ← SubstitutabilityHyp.parse e
      let substHyp := substHyp.get! -- is not none, but ugly 
      return .substitutabilityHyp { substHyp with name := name }
    else if isPositivityHyp type then 
      let posHyp ← PositivityHyp.parse e 
      let posHyp := posHyp.get! 
      return .positivityHyp { posHyp with name := name }
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
  | substitutabilityHyp h => []
  | freshnessHyp h => []
  | positivityHyp h => []
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
  | substitutabilityHyp _ => []
  | freshnessHyp _ => [] 
  | positivityHyp _ => [] 
  | wrong _ => []

def getSubstitutabilityHyps (prf : IRProof) : List SubstitutabilityHyp := 
  match prf with 
  | axK _ _ => [] 
  | axS _ _ _ => []
  | dne _ => []
  | modusPonens _ _ h₁ h₂ => h₁.getSubstitutabilityHyps ++ h₂.getSubstitutabilityHyps 
  | existQuan _ _ _ sfi => sfi.getSubstitutabilityHyps
  | existGen _ _ _ nfv h => nfv.getSubstitutabilityHyps ++ h.getSubstitutabilityHyps
  | existence _ => []
  | substitution _ _ _ sfi h => sfi.getSubstitutabilityHyps ++ h.getSubstitutabilityHyps 
  | knasterTarski _ _ _ sfi h => sfi.getSubstitutabilityHyps ++ h.getSubstitutabilityHyps 
  | prefixpoint _ _ hpos sfi => hpos.getSubstitutabilityHyps ++ sfi.getSubstitutabilityHyps 
  | hyp _ _ => []
  | substitutabilityHyp h => [h]
  | freshnessHyp _ => [] 
  | positivityHyp _ => [] 
  | wrong _ => []

def createEnv (proof : IRProof) : Env := 
  let patternsEnv := proof.getPatterns.map IRPatt.createEnv |>.foldl (init := ({} : Env)) (Env.merge)
  let hypEnvs' : List (String × String) := proof.getHyps.map <| fun ⟨name, assertion⟩ => ⟨name, toString assertion⟩
  let hypEnv:= ({} : Env).addEssentials hypEnvs'
  patternsEnv ++ hypEnv


def toMMString (proof : IRProof) : String :=
  match proof with 
  | axK φ ψ => 
    s! "{φ.toMMInProof} {ψ.toMMInProof} proof-rule-prop-1"
  | axS φ ψ χ => 
    s! "{φ.toMMInProof} {ψ.toMMInProof} {χ.toMMInProof} proof-rule-prop-2"
  | dne φ => 
    s! "{φ.toMMInProof} proof-rule-prop-3"
  | modusPonens φ ψ hφ hφψ => 
    s! "{φ.toMMInProof} {ψ.toMMInProof} {hφ.toMMString} {hφψ.toMMString} proof-rule-mp"
  | existQuan φ x y sfi => 
    s! "{φ.toMMInProof} {x.toMMInProof} {y.toMMInProof} {sfi.toMMString} proof-rule-exists"
  | existence x => 
    s! "{x.toMMInProof} proof-rule-existence" 
  | hyp name _ => name
  | substitutabilityHyp h => h.name
  | freshnessHyp h => h.name 
  | positivityHyp h => h.name
  | _ => "toMMString not implemented"
