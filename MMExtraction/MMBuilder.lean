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
| floating | essential 
  deriving Inhabited, Repr, DecidableEq

instance : ToString HypKind where 
  toString k := match k with 
  | .floating => "f"
  | .essential => "e"

/--
  A Metamath hypothesis made of
  * `label : String` 
  * `stmt : String`
  * `kind : HypKind`.
  The intended meaning is for such an object to represent the Metamath statement of the form 
  `"label $kind stmt $."` where `kind` will be wither `e` or `f`.
-/
structure Hypothesis where 
  label : String 
  stmt : String 
  kind : HypKind
  deriving Inhabited, Repr, DecidableEq

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
-/
structure Env where 
  metavars : List String := [] -- should have no duplicates 
  floatings : List Hypothesis := [] 
  essentials : List Hypothesis := []
  containsWrong : Bool := false
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
    s! "essential: {env.essentials} {endl}"

  instance : ToString Env := ⟨Env.toString⟩

  def addMetavar (env : Env) (mv : String) : Env := 
    { env with metavars := mv :: env.metavars }

  def addFloating (env : Env) (label : String) (stmt : String) : Env := 
    { env with floatings := ⟨label, stmt, .floating⟩ :: env.floatings}

  def addEssential (env : Env) (label : String) (stmt : String) : Env := 
    { env with essentials := ⟨label, stmt, .essential⟩ :: env.essentials}

  def addEssentials (env : Env) (essentials : List (String × String)) : Env := Id.run do 
    -- dirty 
    let mut newenv ← env 
    for essential in essentials do  
      newenv ← newenv.addEssential essential.1 essential.2
    newenv

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

  -- def renameMetavarUnhygienic (env : Env) (old new : String) : Env := {
  --   metavars := env.metavars.replace old new 
  --   .. 
  -- }


end Env 



/--
  The kind of pattern in Metamath representation. It can be either 
  * pattern 
  * evar 
  * svar 
  * wrong
-/
inductive MMPattKind where 
| pattern | evar | svar | wrong 
  deriving DecidableEq, Inhabited, Repr

instance : ToString MMPattKind where 
  toString := fun kind => match kind with 
  | .pattern => "pattern"
  | .evar => "evar"
  | .svar => "svar"
  | .wrong => "wrong"

def MMPattKind.fromType (type : Expr) : MMPattKind := 
  if type.isAppOf `ML.Pattern then .pattern 
  else if type.isAppOf `ML.EVar then .evar 
  else if type.isAppOf `ML.SVar then .svar 
  else .wrong 

/--
  The Metamath syntax of patterns. The main difference between `MMPatt` and `IRPatt` (for now)
  is that an `MMPatt` cannot be a substitution.
-/
inductive MMPatt : Type where 
| metavar (kind : MMPattKind) (name : String) : MMPatt 
| var : MMPatt → MMPatt
| bot : MMPatt
| imp : MMPatt → MMPatt → MMPatt 
| app : MMPatt → MMPatt → MMPatt 
| and : MMPatt → MMPatt → MMPatt 
| or : MMPatt → MMPatt → MMPatt 
| not : MMPatt → MMPatt 
| exist : MMPatt → MMPatt → MMPatt 
| all : MMPatt → MMPatt → MMPatt
| mu : MMPatt → MMPatt → MMPatt  
| nu : MMPatt → MMPatt → MMPatt  
| wrong (msg : String := "") : MMPatt
  deriving DecidableEq, Repr, Inhabited

namespace MMPatt 

  protected def toString : MMPatt → String 
  | .metavar _ n => n 
  | .var n => n.toString 
  | .bot => "bot"
  | .imp e₁ e₂ => s! "( \\imp {e₁.toString} {e₂.toString} )"
  | .app e₁ e₂ => s! "( \\app {e₁.toString} {e₂.toString} )"
  | .and e₁ e₂ => s! "( \\and {e₁.toString} {e₂.toString} )"
  | .or e₁ e₂ => s! "( \\or {e₁.toString} {e₂.toString} )"
  | .not e => s! "( \\not {e.toString} )"
  | .all v e => s! "( \\forall {v.toString} {e.toString} )"
  | .exist v e => s! "( \\exist {v.toString} {e.toString} )"
  | .mu v e => s! "( \\mu {v.toString} {e.toString} )"
  | .nu v e => s! "( \\nu {v.toString} {e.toString} )"
  | .wrong msg => s! "Not a pattern: {msg}"

  instance : ToString MMPatt := ⟨MMPatt.toString⟩

  def toMMInProof : MMPatt → String 
  | .metavar k n => s! "{n}-is-{k} "
  | .var x => x.toMMInProof ++ "var-is-pattern "
  | .imp e₁ e₂ => e₂.toMMInProof ++ e₁.toMMInProof ++ "imp-is-pattern "
  | .and e₁ e₂ => e₂.toMMInProof ++ e₁.toMMInProof ++ "and-is-pattern "
  | .all x e => x.toMMInProof ++ e.toMMInProof ++ "forall-is-pattern "
  | .exist x e => x.toMMInProof ++ e.toMMInProof ++ "exist-is-pattern "
  | _ => ""

end MMPatt 


structure MMProof where 
  label : String 
  env : Env 
  proof : String 
  conclusion : MMPatt 
  deriving DecidableEq, Inhabited, Repr

namespace MMProof 

  def toMM (prf : MMProof) : String := 
    let metavarsStr : String := prf.env.metavars.foldl (init := "") (.++" "++.)
    let floatingsStr := prf.env.floatings.map Hypothesis.toMM |>.foldl (init := "") (.++"\n"++.)
    s! "$v {metavarsStr} $v." ++ "\n" 
      ++ floatingsStr ++ "\n"
      ++ prf.label 
      ++ s! "$p |- {toString prf.conclusion} $= {prf.proof} $."

  def containsMetavar (prf : MMProof) : String → Bool := 
    prf.env.containsMetavar

  -- def renameMetavarUnhygienic (prf : MMProof) (old new : String) : MMProof := {
  --   env := prf.env.replace old new 
  --   ..
  -- }

  -- def renameMetavar (prf : MMProof) (old new : String) (hygiene : Bool := true) : MMProof := 
  --   let overshadows := prf.containsMetavar new 
  --   if hygiene && overshadows then 
  --     prf  
  --   else 
      

end MMProof 
