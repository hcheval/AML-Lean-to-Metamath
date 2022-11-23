import Lean 
import MMExtraction.MMBuilder
import MatchingLogic

open Lean Elab Term Meta Syntax 

set_option autoImplicit false

namespace ML.Meta

-- hack
def stripUniqFromMVarId (s : String) : String := s.dropWhile (!Char.isDigit .)

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
| metavar (kind : MMPattKind) (name : String) : IRPatt 
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
  deriving Repr, Inhabited, DecidableEq

protected def IRPatt.toString : IRPatt → String 
| metavar _ n => n 
| var n => n.toString
| bot => "bot"
| imp e₁ e₂ => s! "( \\imp {e₁.toString} {e₂.toString} )"
| app e₁ e₂ => s! "( \\app {e₁.toString} {e₂.toString} )"
| and e₁ e₂ => s! "( \\and {e₁.toString} {e₂.toString} )"
| or e₁ e₂ => s! "( \\or {e₁.toString} {e₂.toString} )"
| not e => s! "( \\not {e.toString} )"
| all v e => s! "( \\forall {v.toString} {e.toString} )"
| exist v e => s! "( \\exist {v.toString} {e.toString} )"
| mu v e => s! "( \\mu {v.toString} {e.toString} )"
| nu v e => s! "( \\nu {v.toString} {e.toString} )"
| subst e₁ e₂ e₃ => s! "{e₁.toString}[{e₂.toString} // {e₃.toString}]"
-- | appcontext c e => s! "{c.toString}[{e.toString}]"
| wrong msg => s! "Not a pattern: {msg}"

instance : ToString IRPatt := ⟨IRPatt.toString⟩

/--
  Given an `e : Expr` of type `Pattern 𝕊`, 
  constructs an `IRPatt` representing the same pattern.
  The Lean metavariables in `e` will become reified via the `metavar` constructor.
-/
partial def patternToIRM (e : Expr) : MetaM IRPatt := do
  if e.isAppOf `ML.Pattern.implication then 
    let p₁ ← patternToIRM e.getAppArgs[1]!  
    let p₂ ← patternToIRM e.getAppArgs[2]! 
    return .imp p₁ p₂
  else if e.isAppOf `ML.Pattern.application then 
    let p₁ ← patternToIRM e.getAppArgs[1]! 
    let p₂ ← patternToIRM e.getAppArgs[2]! 
    return .app p₁ p₂
  else if e.isAppOf `ML.Pattern.conjunction then 
    let p₁ ← patternToIRM e.getAppArgs[1]! 
    let p₂ ← patternToIRM e.getAppArgs[2]! 
    return .and p₁ p₂
  else if e.isAppOf `ML.Pattern.disjunction then 
    let p₁ ← patternToIRM e.getAppArgs[1]! 
    let p₂ ← patternToIRM e.getAppArgs[2]! 
    return .or p₁ p₂
  else if e.isAppOf `ML.Pattern.universal then 
    let pv ← patternToIRM e.getAppArgs[1]!  
    let pe ← patternToIRM e.getAppArgs[2]! 
    return .all pv pe
  else if e.isAppOf `ML.Pattern.existential then 
    let pv ← patternToIRM e.getAppArgs[1]!  
    let pe ← patternToIRM e.getAppArgs[2]! 
    return .exist pv pe
  else if e.isAppOf `ML.Pattern.mu then 
    let pv ← patternToIRM e.getAppArgs[1]!  
    let pe ← patternToIRM e.getAppArgs[2]! 
    return .mu pv pe
  else if e.isAppOf `ML.Pattern.evar then 
    let p ← patternToIRM e.getAppArgs[1]! 
    return .var p
  else if e.isMVar then 
    let name := stripUniqFromMVarId <| toString e.mvarId!.name
    let type ← inferType e
    let kind := MMPattKind.fromType type 
    return .metavar kind name
  else if e.isBVar then -- should never happen
    panic! "Loose bvar encountered"
  else if e.isAppOf `ML.Pattern.substEvar then 
    let target ← patternToIRM e.getAppArgs[1]!  -- the pattern *in which* we substitute (is there a name for this?)
    let var ← patternToIRM e.getAppArgs[2]! 
    let substituent ← patternToIRM e.getAppArgs[3]! 
    return .subst target var substituent
  else 
    return .wrong

-- NOTE: Since now we are working in `MetaM` we could remove the for `IRPattKind` alltogether 
--- and replace it with calls to `inferType`. Is it worth it? 
/--
  Like `patternToIRM` but non-monadic. 
  An additional `kind : MMPattKind` is required instead. 
  When calling this function, `kind` should be given as the expected kind of the 
  pattern being converted (if your `Expr` is a pattern, set `kind := .pattern`, 
  if it is an `EVar`, set `kind := .evar`, etc.).
-/
partial def patternToIR (e : Expr) (kind : MMPattKind) : IRPatt := Id.run do
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
    return .metavar kind name
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
-/
def IRPatt.createEnv (patt : IRPatt) : Env :=  
  match patt with 
  | .metavar k n => 
    ({ } : Env)
      |>.addMetavar n
      |>.addFloating s! "" s! "{n}-is-{k}"
  | .var e => e.createEnv
  | .bot => { }
  | .app e₁ e₂ | .imp e₁ e₂ | .and e₁ e₂ | .or e₁ e₂ => 
    .merge e₁.createEnv e₂.createEnv
  | .not e => e.createEnv 
  | .exist x e | .all x e | .mu x e | .nu x e => .merge x.createEnv e.createEnv
  | .subst e₁ e₂ e₃ => 
    let freshMetavar := s! "S-{e₁}-{e₂}-{e₃}"
    e₁|>.createEnv
      |>.merge e₂.createEnv 
      |>.merge e₃.createEnv 
      |>.addMetavar freshMetavar
      |>.addEssential "" s! "#Substitution {freshMetavar} {e₁} {e₂} {e₃}" 
      |>.addFloating "" s! "{freshMetavar}-is-pattern" 
  | .wrong _ => { containsWrong := true }


/-
  We use `MetaM` just for fresh mvar generation. 
  Maybe it's not worth it and we should instead leave this function pure and 
  produce fresh mvars by hand (we can even choose to work with different names than 
  the automatic `_uniq.x` ones). 
  But doing things by hand will render us unable to use `inferType` from here on. (do we need that?)
-/
/--
  Given `irpatt : IRPatt`, constructs a `mmpatt : MMPatt` and `env : Env`, 
  where `mmpatt` is a representation of `irpatt` within environment `env`.
  The `env` is constructed as the least environment in which `mmpatt` makes sense.
-/
def IRPatt.toMMPattM : IRPatt → MetaM (MMPatt × Env)
| .metavar k n => do 
  return ⟨.metavar k n, ({ } : Env).addMetavar n
                                          |>.addFloating s! "" s! "{n}-is-{k}"⟩
| .var e => do return ⟨.var (← e.toMMPattM).1, (← e.toMMPattM).2⟩
| .bot => do return ⟨.bot , { }⟩
| .app e₁ e₂ => do 
  let ⟨p₁, env₁⟩ ← e₁.toMMPattM 
  let ⟨p₂, env₂⟩ ← e₂.toMMPattM 
  return ⟨.app p₁ p₂, .merge env₁ env₂⟩
| .and e₁ e₂ => do 
  let ⟨p₁, env₁⟩ ← e₁.toMMPattM 
  let ⟨p₂, env₂⟩ ← e₂.toMMPattM 
  return ⟨.and p₁ p₂, .merge env₁ env₂⟩
| .imp e₁ e₂ => do 
  let ⟨p₁, env₁⟩ ← e₁.toMMPattM 
  let ⟨p₂, env₂⟩ ← e₂.toMMPattM 
  return ⟨.imp p₁ p₂, .merge env₁ env₂⟩
| .or e₁ e₂ => do 
  let ⟨p₁, env₁⟩ ← e₁.toMMPattM 
  let ⟨p₂, env₂⟩ ← e₂.toMMPattM 
  return ⟨.or p₁ p₂, .merge env₁ env₂⟩
| .not e => do 
  let ⟨p, env⟩ ← e.toMMPattM 
  return ⟨.not p, env⟩
| .exist x e => do 
  let ⟨px, envx⟩ ← x.toMMPattM 
  let ⟨pe, enve⟩ ← e.toMMPattM 
  return ⟨.exist px pe, .merge envx enve⟩
| .all x e => do 
  let ⟨px, envx⟩ ← x.toMMPattM 
  let ⟨pe, enve⟩ ← e.toMMPattM 
  return ⟨.all px pe, .merge envx enve⟩
| .mu x e => do 
  let ⟨px, envx⟩ ← x.toMMPattM 
  let ⟨pe, enve⟩ ← e.toMMPattM 
  return ⟨.mu px pe, .merge envx enve⟩
| .nu x e => do 
  let ⟨px, envx⟩ ← x.toMMPattM 
  let ⟨pe, enve⟩ ← e.toMMPattM 
  return ⟨.nu px pe, .merge envx enve⟩
| .wrong msg => do return ⟨.wrong msg, { }⟩
| .subst e₁ e₂ e₃ => do
  let ⟨p₁, env₁⟩ ← e₁.toMMPattM 
  let ⟨p₂, env₂⟩ ← e₂.toMMPattM 
  let ⟨p₃, env₃⟩ ← e₃.toMMPattM 
  -- let freshMetavar := toString (← mkFreshExprMVar none).mvarId!.name 
  let freshMetavar := toString (← mkFreshExprMVar none).mvarId!.name
  return ⟨
    .metavar .pattern freshMetavar, 
      env₁
        |>.merge env₂ 
        |>.merge env₃ 
        |>.addMetavar freshMetavar
        |>.addEssential "" s! "#Substitution {freshMetavar} {p₁} {p₂} {p₃}" 
        |>.addFloating "" s! "{freshMetavar}-is-pattern"
  ⟩


/--
  Same as `toMMPattM` but pure.
-/
def IRPatt.toMMPatt (patt : IRPatt) : (MMPatt × Env) := Id.run do match patt with 
| .metavar k n => 
  return ⟨.metavar k n, ({ } : Env).addMetavar n
                                          |>.addFloating s! "" s! "{n}-is-{k}"⟩
| .var e => return ⟨.var (← e.toMMPatt).1, (← e.toMMPatt).2⟩
| .bot => return ⟨.bot , { }⟩
| .app e₁ e₂ => 
  let ⟨p₁, env₁⟩ ← e₁.toMMPatt 
  let ⟨p₂, env₂⟩ ← e₂.toMMPatt 
  return ⟨.app p₁ p₂, .merge env₁ env₂⟩
| .and e₁ e₂ => 
  let ⟨p₁, env₁⟩ ← e₁.toMMPatt 
  let ⟨p₂, env₂⟩ ← e₂.toMMPatt 
  return ⟨.and p₁ p₂, .merge env₁ env₂⟩
| .imp e₁ e₂ => 
  let ⟨p₁, env₁⟩ ← e₁.toMMPatt 
  let ⟨p₂, env₂⟩ ← e₂.toMMPatt 
  return ⟨.imp p₁ p₂, .merge env₁ env₂⟩
| .or e₁ e₂ => 
  let ⟨p₁, env₁⟩ ← e₁.toMMPatt 
  let ⟨p₂, env₂⟩ ← e₂.toMMPatt 
  return ⟨.or p₁ p₂, .merge env₁ env₂⟩
| .not e => 
  let ⟨p, env⟩ ← e.toMMPatt 
  return ⟨.not p, env⟩
| .exist x e => 
  let ⟨px, envx⟩ ← x.toMMPatt 
  let ⟨pe, enve⟩ ← e.toMMPatt 
  return ⟨.exist px pe, .merge envx enve⟩
| .all x e => 
  let ⟨px, envx⟩ ← x.toMMPatt 
  let ⟨pe, enve⟩ ← e.toMMPatt 
  return ⟨.all px pe, .merge envx enve⟩
| .mu x e => 
  let ⟨px, envx⟩ ← x.toMMPatt 
  let ⟨pe, enve⟩ ← e.toMMPatt 
  return ⟨.mu px pe, .merge envx enve⟩
| .nu x e => 
  let ⟨px, envx⟩ ← x.toMMPatt 
  let ⟨pe, enve⟩ ← e.toMMPatt 
  return ⟨.nu px pe, .merge envx enve⟩
| .wrong msg => return ⟨.wrong msg, { }⟩
| .subst e₁ e₂ e₃ =>
  let ⟨p₁, env₁⟩ ← e₁.toMMPatt 
  let ⟨p₂, env₂⟩ ← e₂.toMMPatt 
  let ⟨p₃, env₃⟩ ← e₃.toMMPatt 
  let freshMetavar := s! "S-{p₁}-{p₂}-{p₃}"
  return ⟨
    .metavar .pattern freshMetavar, 
      env₁
        |>.merge env₂ 
        |>.merge env₃ 
        |>.addMetavar freshMetavar
        |>.addEssential "" s! "#Substitution {freshMetavar} {p₁} {p₂} {p₃}" 
        |>.addFloating "" s! "{freshMetavar}-is-pattern"
  ⟩
#print Nat.succ
def isCtorOfFamily (id : Name) (type : Name) : MetaM Bool := do 
  match (← getEnv).find? id with 
  | ConstantInfo.ctorInfo {type := t, ..} => 
    let ⟨_, _, target⟩ ← forallMetaTelescope t
    return target.isAppOf type
  | none => throwError m! "Unknown identifier {id}"
  | _ => return false 

def isCtorOfProof (id : Name) : MetaM Bool := do 
  match (← getEnv).find? id with 
  | ConstantInfo.ctorInfo {type := t, ..} => 
    let ⟨_, _, target⟩ ← forallMetaTelescope t 
    return target.isAppOf `ML.Proof
  | none => throwError m! "Unknown identifier {id}"
  | _ => return false

def isCtorOfPattern (id : Name) : MetaM Bool := do 
  match (← getEnv).find? id with 
  | ConstantInfo.ctorInfo {type := t, ..} => 
    let ⟨_, _, target⟩ ← forallMetaTelescope t 
    return target.isAppOf `ML.Pattern
  | none => throwError m! "Unknown identifier {id}"
  | _ => return false
