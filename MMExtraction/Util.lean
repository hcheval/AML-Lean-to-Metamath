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

infixl:80 (priority := high) "::" => List.cons