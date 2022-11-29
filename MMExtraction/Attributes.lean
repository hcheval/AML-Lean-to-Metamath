import Lean 
import Mathlib

open Lean 

-- DON'T DELETE THIS. USEFUL AS EXAMPLES.
-- initialize toMMAttr : TagAttribute ← registerTagAttribute `to_mm "export to metamath as is"

-- syntax (name := dummy_attr) "dummy_attr"  str : attr
-- initialize registerTraceClass `dummy_attr

-- initialize registerBuiltinAttribute {
--     name := `dummy_attr
--     descr :="dummy_attr print information"
--     add := fun src stx kind => do
--       logInfo "attribute added"
--   }



syntax (name := mm_extern) "mm_extern" str : attr
initialize mmExternAttr : ParametricAttribute String
  ← registerParametricAttribute {
      name := `mm_extern 
      descr := "export this theorem as the specified metamath theorem instead of further reducing its proof"
      getParam := fun name stx => 
        match stx with 
        | `(attr| mm_extern $mmname:str) => return mmname.getString
        | _ => throwError "unexpected `to_mm_as` attributed" 
      afterSet := fun declName mmname => do 
        IO.println s! "{declName} will be exported to metamath as {mmname}"
  }