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