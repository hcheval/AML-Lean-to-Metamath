import Lean
import Mathlib
import MMExtraction.Util
-- import MatchingLogic 

open Lean Elab Term Meta Syntax 

set_option autoImplicit false 

namespace ML.Meta

/--
  The kind of a Metamath hypothesis, which can be either 
  * `floating` or 
  * `essential`.
-/
inductive HypKind where 
| floating | essential | assumption 
  deriving Inhabited, Repr, DecidableEq

instance : ToString HypKind where 
  toString k := match k with 
  | .floating => "f"
  | .essential => "e"
  | .assumption => "a"

abbrev Claim := String 

def Label := String 
  deriving DecidableEq, Inhabited, Repr, ToString 

/--
  A Metamath hypothesis made of
  * `label : String` 
  * `stmt : List String`
  * `kind : HypKind`.
  The intended meaning is for such an object to represent the Metamath statement of the form 
  `"label $kind stmt $."` where `kind` will be wither `e` or `f`.
-/
structure Hypothesis where 
  label : Label 
  stmt : Claim 
  kind : HypKind
  deriving Inhabited, Repr, DecidableEq

namespace Hypothesis

  def mkFloating (label : String) (stmt : Claim) : Hypothesis := 
    ⟨label, stmt, .floating⟩

  def mkEssential (label : String) (stmt : Claim) : Hypothesis := 
    ⟨label, stmt, .essential⟩

  def mkAssumption (label : String) (stmt : Claim) : Hypothesis := 
    ⟨label, stmt, .assumption⟩

end Hypothesis

/--
  Prints a Metamath hypotheses into Metamath format, i.e. 
  `"label $kind stmt $."` where `kind` will be wither `e` or `f`.
-/
def Hypothesis.toMM (hyp : Hypothesis) : String := 
  s! "{hyp.label} ${hyp.kind} {hyp.stmt} $."

instance : ToString Hypothesis := ⟨Hypothesis.toMM⟩

structure Metavar where 
  name : String 
  floating : Hypothesis 
  deriving DecidableEq, Inhabited, Repr 

def Metavar.equalNames : Metavar → Metavar → Bool := (name . == name .)

/--
  Holds the environment of a Metamath theorem and its proof, containing:
  * `metavars` - the list of mentioned necessary variables 
  * `floatings` - the floating assumptions on those variables 
  * `essentials` - the essential assumptions of the theorem
  * `assumption` - the axiom (i.e. `$a` statements) required by the theorem 
-/
structure Env where 
  metavars : Array Metavar := #[]
  essentials : Array Hypothesis := #[]
  assumptions : Array Hypothesis := #[]
  deriving DecidableEq, Inhabited, Repr



namespace Env 



  protected def toString (env : Env) : String := 
    s! "metavars: {repr env.metavars} {endl}" ++ 
    s! "essential: {env.essentials} {endl}" ++ 
    s! "assumtpions: {env.assumptions} {endl}" 

  instance : ToString Env := ⟨Env.toString⟩

  def addMetavar (env : Env) (mv : Metavar) : Env := 
    { env with metavars := env.metavars.insertP (Metavar.equalNames) mv }

  def addEssentialHyp (env : Env) (hyp : Hypothesis) : Env := 
    { env with essentials := env.essentials.insert hyp }

  def addEssential (env : Env) (label : String) (stmt : Claim) : Env := 
    { env with essentials := env.essentials.insert ⟨label, stmt, .essential⟩}

  def addAssumption (env : Env) (label : String) (stmt : Claim) : Env := 
    { env with assumptions := env.assumptions.insert <| .mkAssumption label stmt }

  def addAssumptionHyp (env : Env) (hyp : Hypothesis) : Env := 
    { env with essentials := env.assumptions.insert hyp }

  def addEssentials (env : Env) (essentials : List (String × String)) : Env := Id.run do 
    -- dirty 
    let mut newenv ← env 
    for essential in essentials do  
      newenv ← newenv.addEssential essential.1 essential.2
    newenv

  def addVar (env : Env) (name : String) : Env :=
    env.addMetavar ⟨name, ⟨s!"{name}-is-var", s! "#Variable {name}", .floating⟩⟩

  def addElementVar (env : Env) (name : String) : Env := 
    env.addMetavar ⟨name, s!"{name}-is-element-var", s!"#ElementVariable {name}", .floating⟩ 

  def addSetVar (env : Env) (name : String) : Env := 
    env.addMetavar ⟨name, s!"{name}-is-element-var", s!"#SetVariable {name}", .floating⟩

  def addSymbol (env : Env) (name : String) : Env := 
    env.addMetavar ⟨name, ⟨s!"{name}-is-symbol", s!"#Symbol {name}", .floating⟩⟩ 

  def metavarIsPattern (mv : Metavar) : Bool := 
    mv.floating.stmt = s!"{mv.name}-is-pattern"

  
  def merge (env₁ env₂ : Env) : Env := Id.run do 
    let mut result : Env := env₁ 
    for mv in env₂.metavars do 
      result := result.addMetavar mv
    for essential in env₂.essentials do 
      result := result.addEssentialHyp essential
    for assumption in env₂.assumptions do 
      result := result.addAssumptionHyp assumption 
    return result 
    
  instance : Append Env := ⟨merge⟩


  def containsMetavar (env : Env) : Metavar → Bool := 
    env.metavars.contains 

end Env 

inductive MMProof where 
| app : String → List MMProof → MMProof 
| incomplete 
  deriving BEq, Inhabited, Repr 



partial def MMProof.toMM (proof : MMProof) : String := 
  match proof with 
  | app head args => joinWith (args.map MMProof.toMM) " " ++ " " ++ head
  | incomplete => "?"

inductive MMTheoremKind where
  | logical | positive | negative | fresh | substitution | context 
  deriving DecidableEq, Inhabited, Repr 

def MMTheoremKind.toLeadingToken : MMTheoremKind → String 
  | logical => "|-"
  | positive => "#Positive"
  | negative => "#Negative"
  | fresh => "#Fresh"
  | substitution => "#Substitution"
  | context => "#ApplicationContext"


structure MMTheorem where 
  label : String 
  env : Env 
  proof : MMProof 
  conclusion : String 
  kind : MMTheoremKind 
  deriving BEq, Inhabited, Repr

namespace MMTheorem 

  def toMM (thm : MMTheorem) : String := 
    let metavarsStr : String := thm.env.metavars.map Metavar.name |>.foldl (init := "") (.++" "++.)
    let floatingsStr := thm.env.metavars.map Metavar.floating |>.map Hypothesis.toMM |>.foldl (init := "") (.++⟨[endl]⟩++.)
    let essentialsStr := thm.env.essentials.map Hypothesis.toMM |>.foldl (init := "") (.++⟨[endl]⟩++.)
    
    let ⟨beginScope, endScope⟩ : String × String := 
      if essentialsStr.length > 0 then ⟨"${", "$}"⟩ else ⟨"", ""⟩

    (if !thm.env.metavars.isEmpty then s!"$v {metavarsStr} $." else "") ++ "\n" 
      ++ (if thm.env.metavars.size > 1 then s!"$d {metavarsStr} $." else "") ++ "\n"
      ++ floatingsStr ++ ⟨[endl]⟩
      ++ beginScope 
      ++ essentialsStr ++ ⟨[endl]⟩
      ++ thm.label ++ " "
      ++ s! "$p {thm.kind.toLeadingToken} {toString thm.conclusion} $= {thm.proof.toMM} $." ++ ⟨[endl]⟩
      ++ endScope

  def containsMetavar (thm : MMTheorem) : Metavar → Bool := 
    thm.env.containsMetavar

end MMTheorem


structure MMFile where 
  theorems : List MMTheorem 
  includes : List System.FilePath 
  rawTheorems : List String := [] 
  deriving BEq, Inhabited, Repr

namespace MMFile 

  def fromMMTheorems (theorems : List MMTheorem) (includes : List System.FilePath := []) : MMFile :=
    {
      includes := includes
      theorems := theorems
    }

  -- dummy implementation 
  def toMM (file : MMFile) : String :=
    let includesStr := 
      file.includes
      |>.map (fun filename => s! "$[ {filename} $]")
      |>.foldl (init := "") (.++⟨[endl]⟩++.)
    includesStr ++ ⟨[endl]⟩ 
      ++ file.rawTheorems.foldl (. ++ "\n" ++ .) ""
      ++ (file.theorems.map MMTheorem.toMM |>.foldl (.++⟨[endl]⟩++.) "")

  def writeToFile (mmfile : MMFile) (fname : System.FilePath) : IO Unit := do 
    IO.FS.writeFile fname mmfile.toMM

end MMFile 

