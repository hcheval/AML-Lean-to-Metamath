import MatchingLogic 
import MMExtraction.MMBuilder
import MMExtraction.ConcreteExporter.ToLabel

namespace ML.MLITP  

open ML.Meta

variable {𝕊 : Type} [ToMMClaim 𝕊]

/--
  `createTempFile φ fname` creates a Metamath file with the unproved statement `φ`.
-/
def createTempFile 
  (φ : Pattern 𝕊) 
  (fname : System.FilePath := "temp.mm")
  : IO Unit := 
do 
  let mmfile : MMFile := {
    includes := ["matching-logic.mm", "matching-logic-propositional.mm"] 
    theorems := [{
      label := φ.toLabel 
      env := {} 
      proof := .incomplete
      conclusion := toMMClaim φ
    }]
  }
  mmfile.writeToFile fname


-- #eval createTempFile (⊥ ⇒ ⊥ : Pattern Empty)    

def _root_.String.findAll (str : String) (p : Char → Bool) : Array String.Pos := 
Id.run do 
  let mut positions : Array String.Pos := #[]
  let mut cursor : String.Pos := 0
  while cursor < str.endPos do 
    if p (str.get! cursor) then 
      positions := positions.push cursor
    cursor := str.next cursor
  return positions 

def extractTheorem (source : String) : String := 
  let «all>» := source.findAll (. == '>')
  Substring.mk source (source.next «all>»[1]!) «all>»[2]! |>.toString

-- Not implemented. It might be useful to get the Metamath proof without its statemenent and the other syntax surrounding it.
def extractProof (source : String) : String := sorry 

def runProverOnFile 
  (fname : System.FilePath)
  (label : String)
  : IO String := 
do 
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["-m", "ml.itp", toString fname, label]
    stdout := IO.Process.Stdio.piped 
    stdin := IO.Process.Stdio.piped 
  }
  child.stdin.putStrLn "tautology"
  child.stdin.putStrLn "proof"
  let stdout ← IO.ofExcept (← IO.asTask child.stdout.readToEnd Task.Priority.dedicated).get
  return extractTheorem stdout  


#eval do IO.println <| (← runProverOnFile "temp.mm" "temp")

def runProver (φ : Pattern 𝕊) (fname : System.FilePath := "temp.mm") : IO String := do 
  createTempFile φ fname 
  runProverOnFile fname φ.toLabel
  
#eval runProver (⊥ ⇒ ⊥ : Pattern Empty) 

-- HACKHACKHACK








def run : IO Unit := do 
  try 
    let output ← IO.Process.output { 
      cmd := "/home/horatiu/metamath-knife/metamath-knife"
      -- args := #["--help"]
      args := #["--verify", "test-extracted.mm"]
    }
    IO.println output.stdout
  catch e =>
    IO.println e

#eval run



  
