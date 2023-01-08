import Lean 
import MMExtraction.MMBuilder
import MatchingLogic

open Lean Elab Term Meta Syntax 


set_option autoImplicit false

namespace ML.Meta

-- hack
def stripUniqFromMVarId (s : String) : String := s.dropWhile (!Char.isDigit .)

/--
  The kind of pattern in Metamath representation. It can be either 
  * pattern 
  * evar 
  * svar 
  * wrong
-/
inductive MetavarKind where 
| pattern | evar | svar | wrong 
  deriving DecidableEq, Inhabited, Repr

def MetavarKind.toLabel (kind : MetavarKind) : String := 
  match kind with 
  | .pattern => "pattern"
  | .evar => "evar"
  | .svar => "svar"
  | .wrong => "wrong"

instance : ToString MetavarKind := ⟨MetavarKind.toLabel⟩

def MetavarKind.toFloatingPredicate (kind : MetavarKind) : String :=
  match kind with 
  | pattern => "#Pattern"
  | evar => "#ElementVariable"
  | svar => "#SetVariable"
  | wrong => "!wrong!"

def MetavarKind.fromType! (type : Expr) : MetavarKind := 
  if type.isAppOf `ML.Pattern then .pattern 
  else if type.isAppOf `ML.EVar then .evar 
  else if type.isAppOf `ML.SVar then .svar 
  else .wrong 



structure Metavar where 
  name : String 
  kind : MetavarKind
  deriving DecidableEq, Inhabited, Repr 

def Metavar.toLabel : Metavar → String 
  | ⟨name, kind⟩ => s! "{name}-is-{kind.toLabel}"

def Metavar.toMMProof : Metavar → MMProof 
  | mv => .app mv.toLabel []

def Metavar.prettifyName : Metavar → Metavar 
  | ⟨name, kind⟩ => 
    let idx := stripUniqFromMVarId name
    let «prefix» := 
      match kind with 
      | .pattern => "ph"
      | .evar => "x"
      | .svar => "X"
      | .wrong => "wrong"
    ⟨«prefix» ++ idx, kind⟩

/-- 
  Represenents a pattern up to exportable constructs. 
  Beyond the primitive constructors, these include derived ones like:
  * universal quantifier
  * conjunction, disjunction, negation 
  * nu.

  Substitutions are also left unfolded in `IRPatt`. 

  Additionally, an `IRPatt` may be a `metavar` representing a generic pattern.
  Metavars will be exported as Metamath variables.

  An `IRPatt` is exported to Metamath into formats, depending on the place of it use: 
  * in statements;
  * in conclusions.
-/
inductive IRPatt : Type where 
| metavar : Metavar → IRPatt 
| var : IRPatt → IRPatt 
| bot : IRPatt
| imp : IRPatt → IRPatt → IRPatt 
| app : IRPatt → IRPatt → IRPatt 
| and : IRPatt → IRPatt → IRPatt 
| or : IRPatt → IRPatt → IRPatt 
| not : IRPatt → IRPatt 
| exist : IRPatt → IRPatt → IRPatt 
| all : IRPatt → IRPatt → IRPatt 
| mu : IRPatt → IRPatt → IRPatt
| nu : IRPatt → IRPatt → IRPatt
| subst : IRPatt → IRPatt → IRPatt → IRPatt
| wrong (msg : String := "") : IRPatt
  deriving Repr, Inhabited, BEq



protected def IRPatt.toClaim : IRPatt → Claim 
| metavar ⟨n, _⟩ => n 
| var n => n.toClaim
| bot => "bot"
| imp e₁ e₂ => s! "( \\imp {e₁.toClaim} {e₂.toClaim} )"
| app e₁ e₂ => s! "( \\app {e₁.toClaim} {e₂.toClaim} )"
| and e₁ e₂ => s! "( \\and {e₁.toClaim} {e₂.toClaim} )"
| or e₁ e₂ => s! "( \\or {e₁.toClaim} {e₂.toClaim} )"
| not e => s! "( \\not {e.toClaim} )"
| all v e => s! "( \\forall {v.toClaim} {e.toClaim} )"
| exist v e => s! "( \\exist {v.toClaim} {e.toClaim} )"
| mu v e => s! "( \\mu {v.toClaim} {e.toClaim} )"
| nu v e => s! "( \\nu {v.toClaim} {e.toClaim} )"
| subst e₁ e₂ e₃ => s! "S-{e₁.toClaim}-{e₂.toClaim}-{e₃.toClaim}"
| wrong msg => s! "Not a pattern: {msg}"

instance : ToString IRPatt := ⟨IRPatt.toClaim⟩ -- temporary 

def mkSubstEvarReplacementMetavarName (target substituted substituent : IRPatt) : String :=
  s! "S-{target}-{substituted}-{substituent}" 

def IRPatt.toMMProof : IRPatt → MMProof 
| metavar mv => mv.toMMProof
| var name => .app "var-is-pattern" [name.toMMProof] 
| imp p₁ p₂ => .app "imp-is-pattern" [p₁.toMMProof, p₂.toMMProof]
| app p₁ p₂ => .app "app-is-pattern" [p₁.toMMProof, p₂.toMMProof]
| and p₁ p₂ => .app "and-is-pattern" [p₁.toMMProof, p₂.toMMProof]
| or p₁ p₂ => .app "or-is-pattern" [p₁.toMMProof, p₂.toMMProof]
| not p => .app "not-is-pattern" [p.toMMProof]
| bot => .app "bot" []
| all v p => .app "forall-is-pattern" [v.toMMProof, p.toMMProof]
| exist v p => .app "exists-is-pattern" [v.toMMProof, p.toMMProof]
| mu v p => .app "forall-is-pattern" [v.toMMProof, p.toMMProof]
| nu v p => .app "forall-is-pattern" [v.toMMProof, p.toMMProof]
| subst target substituted substituent => .app (mkSubstEvarReplacementMetavarName target substituted substituent) []
| wrong msg => .app "wrong" []


/--
  Given an `e : Expr` of type `Pattern 𝕊`, 
  constructs an `IRPatt` representing the same pattern.
  The Lean metavariables in `e` will become reified via the `metavar` constructor.
-/
partial def IRPatt.fromExpr! (e : Expr) : MetaM IRPatt := do
  if e.getAppFn.isConst then 
    match e with 
    | .app (.app (.app (.const `ML.Pattern.implication _) _) p₁) p₂ => 
      let p₁ ← IRPatt.fromExpr! p₁  
      let p₂ ← IRPatt.fromExpr! p₂
      return .imp p₁ p₂
    | .app (.app (.app (.const `ML.Pattern.application _) _) p₁) p₂ => 
      let p₁ ← IRPatt.fromExpr! p₁ 
      let p₂ ← IRPatt.fromExpr! p₂ 
      return .app p₁ p₂
    | .app (.app (.app (.const `ML.Pattern.conjunction _) _) p₁) p₂ => 
      let p₁ ← IRPatt.fromExpr! p₁ 
      let p₂ ← IRPatt.fromExpr! p₂ 
      return .and p₁ p₂
    | .app (.app (.app (.const `ML.Pattern.disjunction _) _) p₁) p₂ => 
      let p₁ ← IRPatt.fromExpr! p₁ 
      let p₂ ← IRPatt.fromExpr! p₂ 
      return .or p₁ p₂
    | .app (.app (.app (.const `ML.Pattern.universal _) _) v) p => 
      let pv ← IRPatt.fromExpr! v  
      let pe ← IRPatt.fromExpr! p
      return .all pv pe
    | .app (.app (.app (.const `ML.Pattern.existential _) _) v) p => 
      let pv ← IRPatt.fromExpr! v  
      let pe ← IRPatt.fromExpr! p 
      return .exist pv pe
    | .app (.app (.app (.const `ML.Pattern.mu _) _) v) p => 
      let pv ← IRPatt.fromExpr! v  
      let pe ← IRPatt.fromExpr! p 
      return .mu pv pe
    | .app (.app (.const `ML.Pattern.evar _) _) v => 
      let p ← IRPatt.fromExpr! v
      return .var p
    | .app (.app (.app (.app (.const `ML.Pattern.substEvar _) _) target) substituted) substituent => 
      let target ← IRPatt.fromExpr! target -- the pattern *in which* we substitute (is there a name for this?)
      let substituted ← IRPatt.fromExpr! substituted 
      let substituent ← IRPatt.fromExpr! substituent 
      return .subst target substituted substituent
    | _ => return .wrong 
  else if e.isMVar then 
    let name := toString e.mvarId!.name
    let type ← inferType e
    let kind := MetavarKind.fromType! type 
    return .metavar <| Metavar.prettifyName ⟨name, kind⟩
  else if e.isBVar then -- should never happen
    panic! "Loose bvar encountered"
  else 
    return .wrong

-- NOTE: Since now we are working in `MetaM` we could remove the for `IRPattKind` alltogether 
--- and replace it with calls to `inferType`. Is it worth it? 
/--
  Like `IRPatt.fromExpr!` but non-monadic. 
  An additional `kind : MetavarKind` is required instead. 
  When calling this function, `kind` should be given as the expected kind of the 
  pattern being converted (if your `Expr` is a pattern, set `kind := .pattern`, 
  if it is an `EVar`, set `kind := .evar`, etc.).
-/
@[deprecated] 
partial def patternToIR (e : Expr) (kind : MetavarKind) : IRPatt := Id.run do
  if e.isAppOf `ML.Pattern.implication then 
    let p₁ ← patternToIR e.getAppArgs[1]! .pattern 
    let p₂ ← patternToIR e.getAppArgs[2]! .pattern 
    return .imp p₁ p₂
  else if e.isAppOf `ML.Pattern.application then 
    let p₁ ← patternToIR e.getAppArgs[1]! .pattern 
    let p₂ ← patternToIR e.getAppArgs[2]! .pattern 
    return .app p₁ p₂
  else if e.isAppOf `ML.Pattern.conjunction then 
    let p₁ ← patternToIR e.getAppArgs[1]! .pattern 
    let p₂ ← patternToIR e.getAppArgs[2]! .pattern 
    return .and p₁ p₂
  else if e.isAppOf `ML.Pattern.disjunction then 
    let p₁ ← patternToIR e.getAppArgs[1]! .pattern 
    let p₂ ← patternToIR e.getAppArgs[2]! .pattern 
    return .or p₁ p₂
  else if e.isAppOf `ML.Pattern.universal then 
    let pv ← patternToIR e.getAppArgs[1]! .evar 
    let pe ← patternToIR e.getAppArgs[2]! .pattern
    return .all pv pe
  else if e.isAppOf `ML.Pattern.existential then 
    let pv ← patternToIR e.getAppArgs[1]! .evar 
    let pe ← patternToIR e.getAppArgs[2]! .pattern
    return .exist pv pe
  else if e.isAppOf `ML.Pattern.evar then 
    let p ← patternToIR e.getAppArgs[1]! .evar
    return .var p
  else if e.isMVar then 
    let name := stripUniqFromMVarId <| toString e.mvarId!.name
    return .metavar ⟨name, kind⟩
  else if e.isBVar then -- should never happen
    return .wrong "loose bvar encountered"
  else if e.isAppOf `ML.Pattern.substEvar then 
    let target ← patternToIR e.getAppArgs[1]! .pattern -- the pattern *in which* we substitute (is there a name for this?)
    let var ← patternToIR e.getAppArgs[2]! .evar
    let substituent ← patternToIR e.getAppArgs[3]! .pattern
    return .subst target var substituent
  else 
    return .wrong 



/--
  Given `patt : IRPatt`, constructs a Metamath environment in which `patt` makes sense.
  This means adding a floating assumption 
-/
def IRPatt.createEnv (patt : IRPatt) : Env :=  
  match patt with 
  | .metavar ⟨name, kind⟩ => 
    ({ } : Env)
      |>.addMetavar name
      |>.addFloating s! "{name}-is-{kind}" s! "{kind.toFloatingPredicate} {name}"
  | .var e => e.createEnv
  | .bot => { }
  | .app e₁ e₂ | .imp e₁ e₂ | .and e₁ e₂ | .or e₁ e₂ => 
    .merge e₁.createEnv e₂.createEnv
  | .not e => e.createEnv 
  | .exist x e | .all x e | .mu x e | .nu x e => .merge x.createEnv e.createEnv
  | .subst e₁ e₂ e₃ => 
    let freshMetavar := mkSubstEvarReplacementMetavarName e₁ e₂ e₃
    e₁|>.createEnv
      |>.merge e₂.createEnv 
      |>.merge e₃.createEnv 
      |>.addMetavar freshMetavar
      |>.addEssential freshMetavar s! "#Substitution {freshMetavar} {e₁} {e₂} {e₃}" 
      |>.addFloating "" s! "{freshMetavar}-is-pattern" 
  | .wrong _ => { }


def isCtorOfFamily (ctorName : Name) (type : Name) : MetaM Bool := do 
  match (← getEnv).find? ctorName with 
  | ConstantInfo.ctorInfo {type := t, ..} => 
    let ⟨_, _, target⟩ ← forallMetaTelescope t
    return target.isAppOf type
  | none => throwError m! "Unknown identifier {ctorName}"
  | _ => return false 

def isCtorOfProof (ctorName : Name) : MetaM Bool := isCtorOfFamily ctorName `ML.Proof

def isCtorOfPattern (ctorName : Name) : MetaM Bool := isCtorOfFamily ctorName `ML.Pattern
