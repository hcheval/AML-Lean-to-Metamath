import Lean 
import Lean.Elab.Command

set_option autoImplicit false 

namespace ML.Meta

open Lean Elab Term Meta Syntax 

def forallSourcesCore : Expr → List (Name × Expr)
| .forallE binder source target _ => (binder, source) :: (forallSourcesCore <| target)
| _ => []

def forallSources (e : Expr) : List (Name × Expr) := 
  forallSourcesCore e

def forallTarget : Expr → Expr 
| .forallE _ _ target _ => forallTarget target 
| e@_ => e
    
def getFunArgs : Expr → List (Name × Expr) 
| .lam bnd arg val _ => (bnd, arg) :: getFunArgs val 
| e@_ => []

def getFunVal : Expr → Expr 
| .lam _ _ val _ => getFunVal val
| e@_ => e 

def letsToList : Expr → List (Name × Expr × Expr) 
| .letE bnd type dfn body _ => (bnd, type, dfn) :: letsToList body 
| _ => []

def liftExprToSyntax {α : Type} (f : Expr → α) : TermElabM Syntax → TermElabM α := fun stx => do 
  let e := elabTermAndSynthesize (← stx) none
  return f (← e)

def termElabMExprToSyntax {α : Type} (f : TermElabM Expr → TermElabM α) : TermElabM Syntax → TermElabM α := fun stx => do 
  let e := elabTermAndSynthesize (← stx) none 
  f e

protected def lift {α} := @liftExprToSyntax α

-- def getDef (id : Name) : MetaM Format := do 
--   let env ← getEnv
--   match env.find? id with 
--   | some (ConstantInfo.defnInfo defnVal) => ppExpr defnVal.value
--   | none => throwError m! "Unknown identifier {id}"
--   | _ => throwError m! "{id} is not a definition"

def getDefnExprFromId (id : Name) : MetaM Expr := 
  do match (← getEnv).find? id with 
  | ConstantInfo.defnInfo { value := v, .. } => return v 
  | none => throwError m! "Unknown identifier {id}"
  | _ => throwError m! "{id} is not a definition"

