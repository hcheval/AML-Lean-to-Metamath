import Lean
import Mathlib
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
  * `metaVars` - the list of mentioned necessary variables 
  * `floatings` - the floating assumptions on those variables 
  * `essentials` - the essential assumptions of the theorem
-/
structure Env where 
  metaVars : List String := [] -- should have no duplicates 
  floatings : List Hypothesis := [] 
  essentials : List Hypothesis := []
  deriving DecidableEq, Inhabited, Repr

namespace Env 

  def merge (env₁ env₂ : Env) : Env := 
    {
      metaVars := env₁.metaVars ++ env₂.metaVars 
      floatings := env₁.floatings ++ env₂.floatings 
      essentials := env₁.essentials ++ env₂.essentials
    }

  def addMetaVar (env : Env) (mv : String) : Env := 
    { env with metaVars := mv :: env.metaVars }

  def addFloating (env : Env) (label : String) (stmt : String) : Env := 
    { env with floatings := ⟨label, stmt, .floating⟩ :: env.floatings}

  def addEssential (env : Env) (label : String) (stmt : String) : Env := 
    { env with essentials := ⟨label, stmt, .essential⟩ :: env.essentials}

  def metavarIsPattern (env : Env) (mv : String) : Bool := 
    Option.isSome <| env.floatings.find? <| fun hyp => hyp.stmt = s! "{mv}-is-pattern"

  -- TODO: something less stupid
  def eraseDup (env : Env) : Env := 
    { env with 
      metaVars := env.metaVars.eraseDup 
      floatings := env.floatings.eraseDup 
      essentials := env.essentials.eraseDup 
    }

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

/--
  The Metamath syntax of patterns. The main difference between `MMPatt` and `IRPatt` (for now)
  is that an `MMPatt` cannot be a substitution.
-/
inductive MMPatt : Type where 
| metaVar (kind : MMPattKind) (name : String) : MMPatt 
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
  | .metaVar _ n => n 
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

end MMPatt 


structure MMProof where 
  label : String 
  env : Env 
  proof : String 
  conclusion : MMPatt 
  deriving DecidableEq, Inhabited, Repr

namespace MMProof 

  def toMM (prf : MMProof) : String := 
    let metavarsStr : String := prf.env.metaVars.foldl (init := "") (.++" "++.)
    let floatingsStr := prf.env.floatings.map Hypothesis.toMM |>.foldl (init := "") (.++"\n"++.)
    s! "$v {metavarsStr} $v." ++ "\n" 
      ++ floatingsStr ++ "\n"
      ++ prf.label 
      ++ s! "$p {toString prf.conclusion} $= {prf.proof} $."

end MMProof 
