import Lean 

open Lean 

initialize toMMAttr : TagAttribute ← registerTagAttribute `to_mm "export to metamath as is"

syntax (name := dummy_attr) "dummy_attr"  str : attr
initialize registerTraceClass `dummy_attr

initialize registerBuiltinAttribute {
    name := `dummy_attr
    descr :="dummy_attr print information"
    add := fun src stx kind => do
      logInfo "attribute added"
  }