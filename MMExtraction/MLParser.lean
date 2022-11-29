import Lean
import MatchingLogic.Proof 
import MMExtraction.MMBuilder
import MMExtraction.IntermediateRepresentation
import MMExtraction.Attributes

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
  /-
    premises we care about are the following:
    * ml-premises 
    * substitutability 
    * (not) free-variableness 
  -/
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
  Given a Matching Logic theorem `def id : Γ ⊢ φ₁ → ... → Γ ⊢ φₙ → Γ ⊢ ψ := prf`,
  `parseMLStmt id` returns a `MLTheorem` with 
  * `conclusion := ψ`
  * `proof := prf`
  * `premises := [φ₁, ..., φₙ]` 
  * `name := id`.
-/
def parseMLTheorem (id : Name) : MetaM MLTheorem := do 
  let defnValue ← getDefnValue id
  let defnValue ← etaExpand defnValue 
  let ⟨_, _, body⟩ ← lambdaMetaTelescope defnValue 
  -- assuming `type` is non-dependent
  let type ← inferType <| ← whnf body 
  let ⟨_, _, targetType⟩ ← forallMetaTelescope type 
  guard <| targetType.isAppOf `ML.Proof  
  return { 
    conclusion := targetType.getAppArgs[2]!
    proof := body 
    name := id
  }









