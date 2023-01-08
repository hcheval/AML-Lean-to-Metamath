import Lean
import MatchingLogic.Proof 
import MMExtraction.MMBuilder
import MMExtraction.IRProofStructured
import MMExtraction.Attributes
import MMExtraction.Tests

open Lean Elab Term Meta Syntax 

set_option autoImplicit false 

namespace ML.Meta 


/--
  Stores a "parsed" Matching Logic statement with fields:
  * `label : Option Name` 
  * `proof : Expr`
  * `conclusion : Expr := inferType proof`.
  The `name` and `premises` fields are optional.
-/
structure MLTheorem where 
  name : Option Name := none 
  conclusion : Expr 
  proof : Expr
  deriving Repr

/--
  `isOfTypeMLProof e` returns `true` iff the type of `e` is of the form `Γ ⊢ φ`.
-/
def isOfTypeMLProof : Expr → MetaM Bool := 
  fun e => do return Expr.isAppOf (← inferType e) `ML.Proof





-- TO REMEMBER: meta-telescopes should only be called once! A subsequent call will give fresh mvars, thus breaking coherence
/--
  Given a Matching Logic theorem `def declName : Γ ⊢ φ₁ → ... → Γ ⊢ φₙ → Γ ⊢ ψ := prf`,
  `parseMLStmt declName` returns a `MLTheorem` with 
  * `conclusion : Expr := ψ`
  * `proof : Expr := prf`
  * `name : Option Expr := declName`.

  The `proof` will be fully eta-expanded and with all bound variables 
  replaced by metavariables.
-/
def parseMLTheorem (declName : Name) : MetaM MLTheorem := do 
  let defnValue ← getDefnValue declName
  let defnValue ← etaExpand defnValue 
  let ⟨_, _, body⟩ ← lambdaMetaTelescope defnValue 
  let type ← inferType <| ← whnf body 
  -- guard <| isNotDependentForall type 
  if !isNotDependentForall type 
    then throwError m! "Unexpected dependent arrow in {type}" 
  let ⟨_, _, targetType⟩ ← forallMetaTelescope type 
  -- guard <| targetType.isAppOf `ML.Proof
  if !targetType.isAppOf `ML.Proof 
    then throwError m! "{declName} is not a Matching Logic theorem"
  return { 
    conclusion := targetType.getAppArgs[2]!
    proof := body 
    name := declName
  }

def MLTheorem.toIRTheorem (thm : MLTheorem) : MetaM IRTheorem := do 
  let irproof ← IRProof.fromExpr! thm.proof 
  return {
    label := toString thm.name.get! 
    proof := irproof 
    conclusion := ← IRPatt.fromExpr! thm.conclusion 
    env := irproof.createEnv.eraseDup
  }

#eval show MetaM _ from do  
  let mlThm ← parseMLTheorem ``Tests.modusPonensTest4
  IO.println <| mlThm.proof
  let irThm : IRTheorem ← mlThm.toIRTheorem
  let mmThm : MMTheorem := irThm.toMMTheorem
  let mmFile : MMFile := .fromMMTheorems [mmThm]
  IO.println <| mmFile.toMM


def exampleExtraction : MetaM Unit := do 
  let mlThm ← parseMLTheorem ``Tests.modusPonensTest4
  let irThm ← mlThm.toIRTheorem 
  let mmThm := irThm.toMMTheorem 
  let mmFile : MMFile := .fromMMTheorems [mmThm]
  mmFile.writeToFile "example-file.mm"

#eval exampleExtraction


#eval show MetaM _ from do
  let stx : Syntax ← `((1 + 2 : Nat)) 
  let e := elabTermAndSynthesize stx none 
  return e