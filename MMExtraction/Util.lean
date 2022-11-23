import Lean 

open Lean Meta Elab Term Syntax 

set_option autoImplicit false 

namespace ML.Meta 


def endl : Char := ⟨10, by simp⟩

def getDefnValue (n : Name) : MetaM Expr := do 
  match (← getEnv).find? n with 
  | ConstantInfo.defnInfo { value := v, .. } => return v 
  | none => throwError m! "Unknown identifier {n}"
  | _ => throwError m! "{n} is not a definition"

