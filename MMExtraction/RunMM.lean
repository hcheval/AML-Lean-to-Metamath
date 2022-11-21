

set_option autoImplicit false

#check IO.println

def runMMOnFile (pathToMM : System.FilePath := "mm") (fname : System.FilePath) : IO Unit := do 
  let mmprocess ← IO.Process.spawn {
    cmd := toString pathToMM
    args := #[toString fname]
  }
  let _ ← mmprocess.wait
  return 


