import Lean 

open Lean Meta Elab Term Syntax 

set_option autoImplicit false 

namespace ML.Meta 


def endl : Char := ⟨10, by simp⟩