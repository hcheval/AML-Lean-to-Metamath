import Lean 
import Mathlib

open Lean 

syntax (name := mm_extern) "mm_extern" str : attr
initialize mmExternAttr : ParametricAttribute String
  ← registerParametricAttribute {
      name := `mm_extern 
      descr := "export this theorem as the specified metamath theorem instead of further reducing its proof"
      getParam := fun name stx => 
        match stx with 
        | `(attr| mm_extern $mmname:str) => return mmname.getString
        | _ => throwError "unexpected `mm_extern` attribute" 
      afterSet := fun declName mmname => do 
        IO.println s! "{declName} will be exported to metamath as {mmname}"
   }


syntax (name := for_matching_logic) "for_matching_logic" : attr 
initialize forMatchingLogicAttr : ParametricAttribute Unit 
  ← registerParametricAttribute {
      name := `for_matching_logic
      descr := "This declaration should be moved to the `MatchingLogic` project because it is not specific to the Metamath extraction, but is potentially useful for the main formalization."
      getParam := fun _ _ => do return 
      afterSet := fun declName _ => do IO.println s!"Declaration {declName} should be moved to the `MatchingLogic` project because it is not specific to the Metamath extraction, but is potentially useful for the main formalization."
   }


syntax (name := rename_to) "rename_to" str : attr 
initialize renameToAttr : ParametricAttribute String 
  ← registerParametricAttribute {
      name := `rename_to 
      descr := "This declaration should be renamed"
      getParam := fun name stx => 
        match stx with 
        | `(attr| rename_to $newName:str) => return newName.getString 
        | _ => throwError "Unexpected `rename_to` attribute"
      afterSet := fun declName newName => do 
        IO.println s!"{declName} should be renamed to {newName}"
    }

-- initialize forMatchingLogicAttr : TagAttribute 
--   ← registerTagAttribute 
--       (name := `for_matching_logic) 
--       (descr := "This declaration should be moved to the `MatchingLogic` project because it is not specific to the Metamath extraction, but is potentially useful for the main formalization.")