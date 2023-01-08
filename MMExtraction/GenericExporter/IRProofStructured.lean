import Lean 
import MMExtraction.MMBuilder
import MMExtraction.IRPatt
import MMExtraction.Attributes
import MatchingLogic

open Lean Elab Term Meta Syntax 

set_option autoImplicit false

namespace ML.Meta

structure Premise where 
  name : String 
  assertion : IRPatt 
  deriving BEq, Inhabited, Repr 

structure SubstitutabilityHyp where 
  name : String := "" 
  target : IRPatt 
  substituent : IRPatt 
  var : IRPatt 
  deriving Inhabited, Repr, BEq 

def isSubstitutabilityHyp (e : Expr) : Bool := 
  e.isAppOf `ML.Pattern.substitutableForEvarIn

def SubstitutabilityHyp.fromExpr? (e : Expr) : MetaM (Option SubstitutabilityHyp) := do
  if e.isAppOf `ML.Pattern.substitutableForEvarIn then 
    let var ← IRPatt.fromExpr! e.getAppArgs[1]!
    let target ← IRPatt.fromExpr! e.getAppArgs[2]!
    let substituent ← IRPatt.fromExpr! e.getAppArgs[3]!
    return some { var := var, substituent := substituent, target := target}
  else return none 

structure FreshnessHyp where 
  name : String := ""
  target : IRPatt 
  var : IRPatt 
  deriving BEq, Inhabited, Repr 

def isFreeEVarHyp (e : Expr) : Bool := 
  e.isAppOf `ML.Pattern.isFreeEvar 

structure PositivityHyp where 
  name : String := ""
  target : IRPatt 
  var : IRPatt 
  deriving Inhabited, Repr, BEq

def isPositivityHyp (e : Expr) : Bool := 
  e.isAppOf `ML.Pattern.Positive 

def PositivityHyp.fromExpr? (e : Expr) : MetaM (Option PositivityHyp) := do 
  if e.isAppOf `ML.Pattern.Positive then 
    let target ← IRPatt.fromExpr! e.getAppArgs[1]!
    let var : IRPatt := .metavar ⟨"?who?", .svar⟩
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
  deriving BEq, Inhabited, Repr 

-- kind of useless
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

-- f e₁   eₙ 
partial def IRProof.fromExpr! (e : Expr) (reducing : Bool := true) : MetaM IRProof := do 
  let e ← if reducing then whnf e else pure e 
  let declName := e.getAppFn.constName! 
  
  if e.isAppOf `ML.Proof.axK then 
    let φ ← IRPatt.fromExpr! e.getAppArgs[2]! 
    let ψ ← IRPatt.fromExpr! e.getAppArgs[3]!
    return .axK φ ψ
  else if e.isAppOf `ML.Proof.axS then 
    let φ ← IRPatt.fromExpr! e.getAppArgs[2]!
    let ψ ← IRPatt.fromExpr! e.getAppArgs[3]!
    let χ ← IRPatt.fromExpr! e.getAppArgs[4]!
    return .axS φ ψ χ
  else if e.isAppOf `ML.Proof.dne then 
    let φ ← IRPatt.fromExpr! e.getAppArgs[2]!
    return .dne φ
  else if e.isAppOf `ML.Proof.modusPonens then 
    let φ := e.getAppArgs[2]! 
    let ψ := e.getAppArgs[3]! 
    let Γφ := e.getAppArgs[4]!
    let Γφimpψ := e.getAppArgs[5]! 
    return .modusPonens (← IRPatt.fromExpr! φ) (← IRPatt.fromExpr! ψ) (← IRProof.fromExpr! Γφ reducing) (← IRProof.fromExpr! Γφimpψ reducing)
  else if e.isAppOf `ML.Proof.existQuan then 
    let φ := e.getAppArgs[2]! 
    let x := e.getAppArgs[3]! 
    let y := e.getAppArgs[4]! 
    let sfi := e.getAppArgs[5]! 
    return .existQuan (← IRPatt.fromExpr! φ) (← IRPatt.fromExpr! x) (← IRPatt.fromExpr! y) (← IRProof.fromExpr! sfi) 
  else if e.isAppOf `ML.Proof.existGen then 
    let φ := e.getAppArgs[2]!
    let ψ := e.getAppArgs[3]!
    let x := e.getAppArgs[4]!
    let nfv := e.getAppArgs[5]!
    let Γφimpψ := e.getAppArgs[6]!
    return .existGen (← IRPatt.fromExpr! φ) (← IRPatt.fromExpr! ψ) (← IRPatt.fromExpr! x) (← IRProof.fromExpr! nfv) (← IRProof.fromExpr! Γφimpψ)
  else if e.isAppOf `ML.Proof.existence then 
    let x ← IRPatt.fromExpr! e.getAppArgs[2]! 
    return .existence x 
  else if e.isAppOf `ML.Proof.substitution then 
    let φ ← IRPatt.fromExpr! e.getAppArgs[2]!
    let ψ ← IRPatt.fromExpr! e.getAppArgs[3]!
    let X ← IRPatt.fromExpr! e.getAppArgs[4]!
    let sfi ← IRProof.fromExpr! e.getAppArgs[5]!
    let h ← IRProof.fromExpr! e.getAppArgs[6]! 
    return .substitution φ ψ X sfi h 
  else if e.isAppOf `ML.Proof.prefixpoint then 
    let φ ← IRPatt.fromExpr! e.getAppArgs[2]!
    let X ← IRPatt.fromExpr! e.getAppArgs[3]! 
    let hpos ← IRProof.fromExpr! e.getAppArgs[4]! 
    let sfi ← IRProof.fromExpr! e.getAppArgs[5]! 
    return .prefixpoint φ X hpos sfi 
  else if e.isAppOf `ML.Proof.knasterTarski then 
    let φ ← IRPatt.fromExpr! e.getAppArgs[2]!
    let ψ ← IRPatt.fromExpr! e.getAppArgs[3]!
    let X ← IRPatt.fromExpr! e.getAppArgs[4]!
    let sfi ← IRProof.fromExpr! e.getAppArgs[5]!
    let h ← IRProof.fromExpr! e.getAppArgs[6]!
    return .knasterTarski φ ψ X sfi h
  else if e.isMVar then 
    let type ← inferType e
    let name := toString e.mvarId!.name 
    if type.isAppOf `ML.Proof then 
      return .hyp name (← IRPatt.fromExpr! type.getAppArgs[2]!)
    if isSubstitutabilityHyp type then 
      let substHyp ← SubstitutabilityHyp.fromExpr? e
      let substHyp := substHyp.get! -- is not none, but ugly 
      return .substitutabilityHyp { substHyp with name := name }
    else if isPositivityHyp type then 
      let posHyp ← PositivityHyp.fromExpr? e 
      let posHyp := posHyp.get! -- is not none, but ugly
      return .positivityHyp { posHyp with name := name }
    else return .wrong (msg := toString type)
  else if e.isSorry then
    return .wrong "sorry"
  else 
    return .wrong 

namespace IRProof 

#eval 1 :: [0, 2]


def getPatterns (prf : IRProof) : List IRPatt :=
  match prf with 
  | axK φ ψ => [φ, ψ] 
  | axS φ ψ χ => [φ, ψ, χ]
  | dne φ => [φ]
  | modusPonens φ ψ h₁ h₂ => .cons φ <| .cons ψ <| h₁.getPatterns ++ h₂.getPatterns
  | existQuan φ x y sfi => sfi.getPatterns.cons φ |>.cons x |>.cons y 
  | existGen φ ψ x nfv Γφimpψ => [φ, ψ, x] ++ nfv.getPatterns ++ Γφimpψ.getPatterns
  | existence x => [x]
  | substitution φ ψ X sfi h => [φ, ψ, X] ++ sfi.getPatterns ++ h.getPatterns 
  | knasterTarski φ ψ X sfi h => [φ, ψ, X] ++ sfi.getPatterns ++ h.getPatterns 
  | prefixpoint φ X hpos sfi => [φ, X] ++ hpos.getPatterns ++ sfi.getPatterns 
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


def toMMProof : IRProof → MMProof 
  | axK φ ψ => 
    .app "proof-rule-prop-1" [φ.toMMProof, ψ.toMMProof]
  | axS φ ψ χ => 
    .app "proof-rule-prop-2" [φ.toMMProof, ψ.toMMProof, χ.toMMProof]
  | dne φ => 
    .app "proof-rule-prop-3" [φ.toMMProof]
  | modusPonens φ ψ hφ hφψ => 
    .app "proof-rule-mp" [φ.toMMProof, ψ.toMMProof, hφ.toMMProof, hφψ.toMMProof]
  | existQuan φ x y sfi => 
    .app "proof-rule-exists" [φ.toMMProof, x.toMMProof, y.toMMProof, sfi.toMMProof]
  | .existGen φ ψ x nfv h =>
    .app "exist-gen" [φ.toMMProof, ψ.toMMProof, x.toMMProof, nfv.toMMProof, h.toMMProof]
  | existence x => 
    .app "proof-rule-existence" [x.toMMProof]
  | hyp name _ => .app name []
  | substitutabilityHyp h => .app h.name []
  | freshnessHyp h => .app h.name []
  | positivityHyp h => .app h.name []
  | substitution φ ψ X sfi h => 
    .app "substitution" [φ.toMMProof, ψ.toMMProof, X.toMMProof, sfi.toMMProof, h.toMMProof] 
  | prefixpoint φ X pos sfi => 
    .app "prefixpoint" [φ.toMMProof, X.toMMProof, pos.toMMProof, sfi.toMMProof]
  | knasterTarski φ ψ X sfi h =>
    .app "knaster-tarski" [φ.toMMProof, ψ.toMMProof, X.toMMProof, sfi.toMMProof, h.toMMProof]
  | wrong msg => .app s! "wrong {msg}" []

end IRProof


structure IRTheorem where 
  label : String 
  proof : IRProof 
  conclusion : IRPatt 
  env : Env 
  deriving BEq, Inhabited, Repr 

namespace IRTheorem

  def toMMTheorem (thm : IRTheorem) : MMTheorem := 
    {
      label := thm.label 
      proof := thm.proof.toMMProof
      conclusion := thm.conclusion.toClaim
      env := thm.env  
    }

end IRTheorem
