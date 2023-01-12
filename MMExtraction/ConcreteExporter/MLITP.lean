import MatchingLogic 
import MMExtraction.MMBuilder
import MMExtraction.ConcreteExporter.ToLabel
import MMExtraction.ConcreteExporter.Var 
import MMExtraction.ConcreteExporter.CreateEnv

set_option autoImplicit false 

namespace ML.MLITP  

open ML.Meta

deriving instance Repr for Pattern 

/--
  `Statement 𝕊` is a statement to be automately proved by invoking the `ml.itp` prover.
  It can be one of:
  * `tautology φ`: a proof that `φ` is a tautology 
  * `positive xX φ`: a proof that `φ` is positive for `xX`
  * `negative xX φ`: a proof that `φ` is negative for `xX` 
  * `fresh xX φ`: a proof that `xX` is fresh in `φ` 
  * `substitution var substituent target result`: a proof that `result = target[var ⇐ substituent]`
  * `context xX c`: proof that `c` is an application context in `xX`.  
-/
inductive Statement (𝕊 : Type) where 
/-- `tautology φ` is the statement that `φ` is a tautology -/
| tautology : Pattern 𝕊 → Statement 𝕊 
/-- `positive xX φ` is the statement that `φ` is positive for `xX` -/
| positive : Var → Pattern 𝕊 → Statement 𝕊 
/-- `negative xX φ` is the statement that `φ` is negative for `xX` -/
| negative : Var → Pattern 𝕊 → Statement 𝕊 
/-- `fresh xX φ` is the statement that `xX` is fresh in `φ` -/
| fresh : Var → Pattern 𝕊 → Statement 𝕊 
/-- 
`substitution var substituent target result` is the statement that `target[var ⇐ substituent] = result`.
The `result` argument has the default value of `target[var ⇐ substituent]`
 -/
| substitution (var : Var) (substituent : Pattern 𝕊) (target : Pattern 𝕊) (result : Pattern 𝕊 := target[var ⇐ substituent]) : Statement 𝕊 
/-- `context xX φ` is the statement that `φ = C[xX]` for some `C : AppContext` -/
| context : Var → Pattern 𝕊 → Statement 𝕊
  deriving DecidableEq, Inhabited, Repr 

variable {𝕊 : Type} [ToMMClaim 𝕊]

def Statement.toLabel (statement : Statement 𝕊) : String := 
  match statement with 
  | tautology φ => s!"__TAUTO__{φ.toLabel}" -- this does not work if the string contains whitespace at the end. Why? 
  | positive xX φ => s! "__POSITIVE__{xX.toPattern 𝕊 |>.toLabel}__{φ.toLabel}"  
  | negative xX φ => s! "__NEGATIVE__{xX.toPattern 𝕊 |>.toLabel}__{φ.toLabel}"  
  | fresh xX φ => s! "__FRESH__{xX.toPattern 𝕊 |>.toLabel}__{φ.toLabel}" 
  | substitution var substituent target result => s! "__SUBST__{var.toPattern 𝕊 |>.toLabel}__{substituent.toLabel}__{target.toLabel}__{result.toLabel}"
  | context xX φ => s! "__CONTEXT__{xX.toPattern 𝕊 |>.toLabel}__{φ.toLabel}" 


protected def Statement.toMMClaim (statement : Statement 𝕊) : String := 
  match statement with 
  | tautology φ => φ.toMMClaim 
  | positive xX φ => xX.toMMClaim ++ " " ++ φ.toMMClaim 
  | negative xX φ => xX.toMMClaim ++ " " ++ φ.toMMClaim 
  | fresh xX φ => xX.toMMClaim ++ " " ++ φ.toMMClaim 
  | substitution var substituent target result => result.toMMClaim ++ " " ++ target.toMMClaim ++ " " ++ substituent.toMMClaim ++ " " ++ var.toMMClaim  
  | context xX φ => xX.toMMClaim ++ " " ++ φ.toMMClaim

def Statement.toMMTheoremKind (statement : Statement 𝕊) : MMTheoremKind :=
  match statement with 
  | tautology _ => .logical 
  | positive _ _ => .positive 
  | negative _ _ => .negative 
  | fresh _ _ => .fresh 
  | substitution _ _ _ _ => .substitution
  | context _ _ => .context

def Statement.createEnv (statement : Statement 𝕊) : Env := 
  match statement with 
  | tautology φ => φ.createEnv 
  | positive xX φ => φ.createEnv.addVar xX.toMMClaim
  | negative xX φ => φ.createEnv.addVar xX.toMMClaim 
  | fresh xX φ => φ.createEnv.addVar xX.toMMClaim 
  | substitution var substituent target result => substituent.createEnv ++ target.createEnv ++ result.createEnv |>.addVar var.toMMClaim 
  | context xX φ => φ.createEnv.addVar xX.toMMClaim

/--
  `createTempFile stmt fname` creates a Metamath file with the unproved statement `stmt`.
-/
def createTempFile 
  (statement : Statement 𝕊) 
  (fname : System.FilePath := "temp.mm")
  (label := statement.toLabel)
  : IO Unit := 
do 
  let mmfile : MMFile := {
    includes := ["matching-logic.mm", "matching-logic-propositional.mm"] 
    theorems := [{
      label := label
      env := statement.createEnv
      proof := .incomplete
      conclusion := statement.toMMClaim 
      kind := statement.toMMTheoremKind
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

inductive ProverCommand where 
  | tautology | positive | negative | fresh | substitution | context 
  deriving BEq, Inhabited, Repr 

protected def ProverCommand.toString : ProverCommand → String 
  | tautology => "tautology"
  | positive => "positive"
  | negative => "negative"
  | fresh => "fresh"
  | substitution => "substitution"
  | context => "context"

instance : ToString ProverCommand := ⟨ProverCommand.toString⟩

def Statement.toProverCommand : Statement 𝕊 → ProverCommand 
  | tautology _ => .tautology 
  | positive _ _ => .positive 
  | negative _ _ => .negative 
  | fresh _ _ => .fresh 
  | substitution _ _ _ _ => .substitution
  | context _ _ => .context

def runProverOnFile 
  (fname : System.FilePath)
  (label : String)
  (command : ProverCommand)
  : IO String := 
do 
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["-m", "ml.itp", toString fname, label]
    stdout := IO.Process.Stdio.piped 
    stdin := IO.Process.Stdio.piped 
  }
  child.stdin.putStrLn command.toString
  child.stdin.putStrLn "proof"
  let stdout ← IO.ofExcept (← IO.asTask child.stdout.readToEnd Task.Priority.dedicated).get
  return extractTheorem stdout  



def runProver (statement : Statement 𝕊) 
  (fname : System.FilePath := "temp.mm") 
  (label := statement.toLabel)
  (command : ProverCommand := statement.toProverCommand)
  (deleteTempFile := false) 
  : IO String :=
do 
  createTempFile statement fname label
  dbg_trace fname
  dbg_trace label 
  dbg_trace command 
  let output ← runProverOnFile fname label command 
  if deleteTempFile then 
    IO.FS.removeFile fname
  return output 
  

#eval runProver (.tautology (⊥ ⇒ ⊥ : Pattern Empty)) 
-- #eval runProver (.fresh (.evar ⟨0⟩) (⊥ ⇒ (.evar ⟨1⟩) : Pattern Empty)) 
-- #eval runProver (.positive (.evar ⟨0⟩) (⊥ ⇒ ⊥ : Pattern Empty))

-- #eval do IO.println <| (← runProverOnFile "temp.mm" "__LP-bot-imp-bot-RP" .tautology)



def normalizeProof 
  (fname : System.FilePath := "temp.mm")
  (label : String)
  : IO String := 
do 
  let child ← IO.Process.spawn {
    cmd := "/home/horatiu/metamath-exe/src/metamath"
    args := #[toString fname]
    stdout := IO.Process.Stdio.piped 
    stdin := IO.Process.Stdio.piped 
  }
  child.stdin.putStrLn s!"show proof {label} /normal"
  let stdout ← IO.ofExcept (← IO.asTask child.stdout.readToEnd Task.Priority.dedicated).get 
  return stdout 


#eval normalizeProof (label := "__SUBST_____x0____bot_____x0____bot")
#check List.isInfix


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

#check IO.Process.Child.wait

