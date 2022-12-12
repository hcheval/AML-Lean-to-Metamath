import Lean 
import MMExtraction.MMBuilder
import MMExtraction.IRPatt
import MMExtraction.IRProofStructured
import MatchingLogic

open Lean Elab Term Meta Syntax 

set_option autoImplicit false

namespace ML.Meta
