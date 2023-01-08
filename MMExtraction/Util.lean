import Lean 

open Lean Meta Elab Term Syntax 

set_option autoImplicit false 

namespace ML.Meta 


def endl : Char := ⟨10, by simp⟩

-- wrong implementation: adds one extra `sep` at the end, doesn't matter
def joinWith (s : List String) (sep : String) : String := 
  s.headD "" ++ (s.tailD [] |>.map (sep ++ .) |>.foldl (. ++ .) (init := ""))

#eval joinWith ["a", "b", "c"] "-"

def isNotDependentForall (e : Expr) : Bool := !(e.isForall && !e.isArrow)

def _root_.Option.get!! {α : Type _} [Inhabited α] : Option α → α 
| some x => x 
| none => panic! "Option.get!! got none value "


/--
  Returns the definition of `declName` or throws an error if `declName` is not a definition.
-/
def getDefnValue (declName : Name) : MetaM Expr := do 
  match (← getEnv).find? declName with 
  | ConstantInfo.defnInfo { value := v, .. } => return v 
  | none => throwError m! "Unknown identifier {declName}"
  | _ => throwError m! "{declName} is not a definition"


@[inline] protected def _root_.List.insertP {α : Type _} (p : α → α → Bool) (a : α) (l : List α) : List α :=
  if l.find? (p a) |>.isSome then l else a :: l

@[inline] protected def _root_.List.unionP {α : Type _} (p : α → α → Bool) (l₁ l₂ : List α)  : List α := List.foldr (.insertP p) l₂ l₁
