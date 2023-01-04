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

/--
  A Metamath hypothesis made of
  * `label : String` 
  * `stmt : List String`
  * `kind : HypKind`.
  The intended meaning is for such an object to represent the Metamath statement of the form 
  `"label $kind stmt $."` where `kind` will be wither `e` or `f`.
-/
structure Hypothesis where 
  label : String 
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

/--
  Holds the environment of a Metamath theorem and its proof, containing:
  * `metavars` - the list of mentioned necessary variables 
  * `floatings` - the floating assumptions on those variables 
  * `essentials` - the essential assumptions of the theorem
  * `assumption` - the axiom (i.e. `$a` statements) required by the theorem 
-/
structure Env where 
  metavars : List String := [] -- should have no duplicates 
  floatings : List Hypothesis := [] 
  essentials : List Hypothesis := []
  assumptions : List Hypothesis := []
  deriving DecidableEq, Inhabited, Repr

namespace Env 

  def merge (env₁ env₂ : Env) : Env := 
    {
      metavars := env₁.metavars ++ env₂.metavars 
      floatings := env₁.floatings ++ env₂.floatings 
      essentials := env₁.essentials ++ env₂.essentials
    }

  instance : Append Env := ⟨merge⟩

  protected def toString (env : Env) : String := 
    s! "metavars: {env.metavars} {endl}" ++ 
    s! "floating: {env.floatings} {endl}" ++ 
    s! "essential: {env.essentials} {endl}" ++ 
    s! "assumtpions: {env.assumptions} {endl}" 

  instance : ToString Env := ⟨Env.toString⟩

  def addMetavar (env : Env) (mv : String) : Env := 
    { env with metavars := mv :: env.metavars }

  def addFloatingHyp (env : Env) (hyp : Hypothesis) : Env := 
    { env with floatings := hyp :: env.floatings }

  def addFloating (env : Env) (label : String) (stmt : Claim) : Env := 
    { env with floatings := ⟨label, stmt, .floating⟩ :: env.floatings}

  def addEssentialHyp (env : Env) (hyp : Hypothesis) : Env := 
    { env with essentials := hyp :: env.essentials }

  def addEssential (env : Env) (label : String) (stmt : Claim) : Env := 
    { env with essentials := ⟨label, stmt, .essential⟩ :: env.essentials}

  def addAssumption (env : Env) (label : String) (stmt : Claim) : Env := 
    { env with assumptions := .mkAssumption label stmt :: env.assumptions }

  def addEssentials (env : Env) (essentials : List (String × String)) : Env := Id.run do 
    -- dirty 
    let mut newenv ← env 
    for essential in essentials do  
      newenv ← newenv.addEssential essential.1 essential.2
    newenv


  def addElementVar (env : Env) (name : String) : Env := 
    env 
      |>.addMetavar name 
      |>.addFloating s!"{name}-is-element-var" s!"#ElementVariable {name}"

  def addSetVar (env : Env) (name : String) : Env := 
    env 
      |>.addMetavar name 
      |>.addFloating s!"{name}-is-element-var" s!"#SetVariable {name}"

  def addSymbol (env : Env) (name : String) : Env := 
    env 
      |>.addMetavar name 
      |>.addFloating s!"{name}-is-symbol" s!"#Symbol {name}"

  def metavarIsPattern (env : Env) (mv : String) : Bool := 
    Option.isSome <| env.floatings.find? <| fun hyp => hyp.stmt = s! "{mv}-is-pattern"

  -- TODO: something less stupid
  def eraseDup (env : Env) : Env := 
    { env with 
      metavars := env.metavars.eraseDup 
      floatings := env.floatings.eraseDup 
      essentials := env.essentials.eraseDup 
    }

  def containsMetavar (env : Env) : String → Bool := 
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

structure MMTheorem where 
  label : String 
  env : Env 
  proof : MMProof 
  conclusion : String 
  deriving BEq, Inhabited, Repr

namespace MMTheorem 

  def toMM (prf : MMTheorem) : String := 
    let metavarsStr : String := prf.env.metavars.foldl (init := "") (.++" "++.)
    let floatingsStr := prf.env.floatings.map Hypothesis.toMM |>.foldl (init := "") (.++⟨[endl]⟩++.)
    let essentialsStr := prf.env.essentials.map Hypothesis.toMM |>.foldl (init := "") (.++⟨[endl]⟩++.)
    
    let ⟨beginScope, endScope⟩ : String × String := 
      if essentialsStr.length > 0 then ⟨"${", "$}"⟩ else ⟨"", ""⟩
    
    (if !prf.env.metavars.isEmpty then s!"$v {metavarsStr} $." else "") ++ "\n" 
      ++ floatingsStr ++ ⟨[endl]⟩
      ++ beginScope 
      ++ essentialsStr ++ ⟨[endl]⟩
      ++ prf.label ++ " "
      ++ s! "$p |- {toString prf.conclusion} $= {prf.proof.toMM} $." ++ ⟨[endl]⟩
      ++ endScope

  def containsMetavar (prf : MMTheorem) : String → Bool := 
    prf.env.containsMetavar

end MMTheorem


structure MMFile where 
  theorems : List MMTheorem 
  includes : List System.FilePath 
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
      ++ file.theorems[0]!.toMM

  def writeToFile (mmfile : MMFile) (fname : System.FilePath) : IO Unit := do 
    IO.FS.writeFile fname mmfile.toMM

end MMFile 

