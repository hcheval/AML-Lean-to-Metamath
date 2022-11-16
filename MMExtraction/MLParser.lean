import Lean
import MatchingLogic.Proof 
import MMExtraction.MMBuilder

open Lean Elab Term Meta Syntax 

set_option autoImplicit false 

namespace ML.Meta 


/--
  Stores a "parsed" Matching Logic statement with fields:
  * `premises : List Expr` 
  * `conclusion : Expr` 
  * `proof : Option Expr`.
-/
structure MLStmt where 
  name : Option Name := none 
  premises : List Expr := []
  conclusion : Expr 
  proof : Option Expr := none
  deriving Repr

/--
  `isOfTypeMLProof e` returns `true` iff the type of `e` is of the form `Γ ⊢ φ`.
-/
def isOfTypeMLProof : Expr → MetaM Bool := 
  fun e => do return Expr.isAppOf (← inferType e) `ML.Proof

def parseMLStmtClaimCore (e : Expr) : MetaM MLStmt := do
  let ⟨args, _, target⟩ ← forallMetaTelescope e
  return {
    conclusion := target.getAppArgs[2]! 
    premises := (← args.toList.mapM inferType).filter <| (Expr.isAppOf . `ML.Proof)
  }

def parseMLStmtProofCore (e : Expr) : MetaM Expr := do 
  let ⟨_, _, body⟩ ← lambdaMetaTelescope e 
  return body 

/--
  Given a Matching Logic proof `def id : Γ ⊢ φ₁ → ... → Γ ⊢ φₙ → Γ ⊢ ψ := prf`,
  `parseMLStmt id` returns a `Stmt` with 
  * `conclusion := ψ`
  * `premises := [φ₁, ..., φₙ]` 
  * `proof := prf`.
-/
def parseMLStmt (id : Name) : MetaM MLStmt := do 
  match (← getEnv).find? id with 
  | ConstantInfo.defnInfo {value := v, ..} => 
    let type ← inferType v
    let stmt ← parseMLStmtClaimCore type
    let prf ← parseMLStmtProofCore v 
    return { stmt with proof := prf, name := id }
  | none => throwError m! "Unknown identifier {id}"
  | _ => throwError "{id} is not a definition"




/-- 
  Represenents a pattern up to exportable constructs. 
-/
inductive IRPatt : Type where 
| metaVar (kind : MMPattKind) (name : String) : IRPatt 
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
  deriving Repr, Inhabited

protected def IRPatt.toString : IRPatt → String 
| metaVar _ n => n 
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
| wrong msg => s! "Not a pattern: {msg}"

instance : ToString IRPatt := ⟨IRPatt.toString⟩

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
    let name := toString e.mvarId!.name
    return .metaVar kind name
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
  Given `e : Expr` supposed to be of type `Pattern 𝕊`, 
  converts an `IRPatt` representing the same pattern.
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
    let name := toString e.mvarId!.name
    let type ← inferType e
    let kind : MMPattKind := 
      if type.isAppOf `ML.Pattern then 
        .pattern 
      else if type.isAppOf `ML.EVar then 
        .evar 
      else if type.isAppOf `ML.SVar then 
        .svar 
      else 
        .wrong 
    return .metaVar kind name
  else if e.isBVar then -- should never happen
    panic! "Loose bvar encountered"
  else if e.isAppOf `ML.Pattern.substEvar then 
    let target ← patternToIRM e.getAppArgs[1]!  -- the pattern *in which* we substitute (is there a name for this?)
    let var ← patternToIRM e.getAppArgs[2]! 
    let substituent ← patternToIRM e.getAppArgs[3]! 
    return .subst target var substituent
  else 
    return .wrong


/-
  We use `MetaM` just for fresh mvar generation. 
  Maybe it's not worth it and we should instead leave this function pure and 
  produce fresh mvars by hand (we can even choose to work with different names than 
  the automatic `_uniq.x` ones). 
  But doing things by hand will render us unable to use `inferType` from here on. (do we need that?)
-/
def IRPatt.toMMPatternM : IRPatt → MetaM (MMPatt × Env)
| .metaVar k n => do 
  return ⟨.metaVar k n, ({ } : Env).addMetaVar n
                                          |>.addFloating s! "" s! "{n}-is-{k}"⟩
| .var e => do return ⟨.var (← e.toMMPatternM).1, (← e.toMMPatternM).2⟩
| .bot => do return ⟨.bot , { }⟩
| .app e₁ e₂ => do 
  let ⟨p₁, env₁⟩ ← e₁.toMMPatternM 
  let ⟨p₂, env₂⟩ ← e₂.toMMPatternM 
  return ⟨.app p₁ p₂, .merge env₁ env₂⟩
| .and e₁ e₂ => do 
  let ⟨p₁, env₁⟩ ← e₁.toMMPatternM 
  let ⟨p₂, env₂⟩ ← e₂.toMMPatternM 
  return ⟨.and p₁ p₂, .merge env₁ env₂⟩
| .imp e₁ e₂ => do 
  let ⟨p₁, env₁⟩ ← e₁.toMMPatternM 
  let ⟨p₂, env₂⟩ ← e₂.toMMPatternM 
  return ⟨.imp p₁ p₂, .merge env₁ env₂⟩
| .or e₁ e₂ => do 
  let ⟨p₁, env₁⟩ ← e₁.toMMPatternM 
  let ⟨p₂, env₂⟩ ← e₂.toMMPatternM 
  return ⟨.or p₁ p₂, .merge env₁ env₂⟩
| .not e => do 
  let ⟨p, env⟩ ← e.toMMPatternM 
  return ⟨.not p, env⟩
| .exist x e => do 
  let ⟨px, envx⟩ ← x.toMMPatternM 
  let ⟨pe, enve⟩ ← e.toMMPatternM 
  return ⟨.exist px pe, .merge envx enve⟩
| .all x e => do 
  let ⟨px, envx⟩ ← x.toMMPatternM 
  let ⟨pe, enve⟩ ← e.toMMPatternM 
  return ⟨.all px pe, .merge envx enve⟩
| .mu x e => do 
  let ⟨px, envx⟩ ← x.toMMPatternM 
  let ⟨pe, enve⟩ ← e.toMMPatternM 
  return ⟨.mu px pe, .merge envx enve⟩
| .nu x e => do 
  let ⟨px, envx⟩ ← x.toMMPatternM 
  let ⟨pe, enve⟩ ← e.toMMPatternM 
  return ⟨.nu px pe, .merge envx enve⟩
| .wrong msg => do return ⟨.wrong msg, { }⟩
| .subst e₁ e₂ e₃ => do
  let ⟨p₁, env₁⟩ ← e₁.toMMPatternM 
  let ⟨p₂, env₂⟩ ← e₂.toMMPatternM 
  let ⟨p₃, env₃⟩ ← e₃.toMMPatternM 
  -- let freshMetavar := toString (← mkFreshExprMVar none).mvarId!.name 
  let freshMetavar := toString (← mkFreshExprMVar none).mvarId!.name
  return ⟨
    .metaVar .pattern freshMetavar, 
      env₁
        |>.merge env₂ 
        |>.merge env₃ 
        |>.addMetaVar freshMetavar
        |>.addEssential "" s! "#Substitution {freshMetavar} {p₁} {p₂} {p₃}" 
        |>.addFloating "" s! "{freshMetavar}-is-pattern"
  ⟩


def IRPatt.toMMPattern : IRPatt → Id (MMPatt × Env)
| .metaVar k n => do 
  return ⟨.metaVar k n, ({ } : Env).addMetaVar n
                                          |>.addFloating s! "" s! "{n}-is-{k}"⟩
| .var e => do return ⟨.var (← e.toMMPattern).1, (← e.toMMPattern).2⟩
| .bot => do return ⟨.bot , { }⟩
| .app e₁ e₂ => do 
  let ⟨p₁, env₁⟩ ← e₁.toMMPattern 
  let ⟨p₂, env₂⟩ ← e₂.toMMPattern 
  return ⟨.app p₁ p₂, .merge env₁ env₂⟩
| .and e₁ e₂ => do 
  let ⟨p₁, env₁⟩ ← e₁.toMMPattern 
  let ⟨p₂, env₂⟩ ← e₂.toMMPattern 
  return ⟨.and p₁ p₂, .merge env₁ env₂⟩
| .imp e₁ e₂ => do 
  let ⟨p₁, env₁⟩ ← e₁.toMMPattern 
  let ⟨p₂, env₂⟩ ← e₂.toMMPattern 
  return ⟨.imp p₁ p₂, .merge env₁ env₂⟩
| .or e₁ e₂ => do 
  let ⟨p₁, env₁⟩ ← e₁.toMMPattern 
  let ⟨p₂, env₂⟩ ← e₂.toMMPattern 
  return ⟨.or p₁ p₂, .merge env₁ env₂⟩
| .not e => do 
  let ⟨p, env⟩ ← e.toMMPattern 
  return ⟨.not p, env⟩
| .exist x e => do 
  let ⟨px, envx⟩ ← x.toMMPattern 
  let ⟨pe, enve⟩ ← e.toMMPattern 
  return ⟨.exist px pe, .merge envx enve⟩
| .all x e => do 
  let ⟨px, envx⟩ ← x.toMMPattern 
  let ⟨pe, enve⟩ ← e.toMMPattern 
  return ⟨.all px pe, .merge envx enve⟩
| .mu x e => do 
  let ⟨px, envx⟩ ← x.toMMPattern 
  let ⟨pe, enve⟩ ← e.toMMPattern 
  return ⟨.mu px pe, .merge envx enve⟩
| .nu x e => do 
  let ⟨px, envx⟩ ← x.toMMPattern 
  let ⟨pe, enve⟩ ← e.toMMPattern 
  return ⟨.nu px pe, .merge envx enve⟩
| .wrong msg => do return ⟨.wrong msg, { }⟩
| .subst e₁ e₂ e₃ => do
  let ⟨p₁, env₁⟩ ← e₁.toMMPattern 
  let ⟨p₂, env₂⟩ ← e₂.toMMPattern 
  let ⟨p₃, env₃⟩ ← e₃.toMMPattern 
  let freshMetavar := s! "S-{p₁}-{p₂}-{p₃}"
  return ⟨
    .metaVar .pattern freshMetavar, 
      env₁
        |>.merge env₂ 
        |>.merge env₃ 
        |>.addMetaVar freshMetavar
        |>.addEssential "" s! "#Substitution {freshMetavar} {p₁} {p₂} {p₃}" 
        |>.addFloating "" s! "{freshMetavar}-is-pattern"
  ⟩



def fresh (n : ℕ) : MetaM Unit :=
match n with 
| 0 => do return 
| n + 1 => do 
  IO.println <| (← mkFreshExprMVar none).mvarId!.name 
  IO.println <| (← mkFreshExprMVar none).mvarId!.name 
  fresh n 

#eval show MetaM Unit from do 
  IO.println <| (← mkFreshExprMVar none) == (← mkFreshExprMVar none) 

#eval show MetaM _ from do 
  let stmt ← parseMLStmt `ML.Proof.univQuan 
  let conclusion : IRPatt ← patternToIRM stmt.conclusion 
  IO.println <| ← ppExpr stmt.conclusion
  IO.println conclusion
  let ⟨exp, env⟩ ← conclusion.toMMPatternM 
  let env := env.eraseDup 
  IO.println env.metaVars
  IO.println env.floatings
  IO.println env.essentials
  IO.println exp

-- implSelf φ 
-- φ-is-pattern implSelf 
def MMPatt.toMMInProof (env : Env) : MMPatt → String 
| .metaVar k n => s! "{n}-is-{k} "
| .var x => x.toMMInProof env ++ "var-is-pattern "
| .imp e₁ e₂ => e₂.toMMInProof env ++ e₁.toMMInProof env ++ "imp-is-pattern "
| .and e₁ e₂ => e₂.toMMInProof env ++ e₁.toMMInProof env ++ "and-is-pattern "
| .all x e => x.toMMInProof env ++ e.toMMInProof env ++ "forall-is-pattern "
| .exist x e => x.toMMInProof env ++ e.toMMInProof env ++ "exist-is-pattern "
| _ => ""




#check @ML.Pattern.conjunction
partial def proofToMM (e : Expr) : MetaM String := do
  let type ← inferType e
  -- IO.println e 
  let ⟨_, _, tgtType⟩ ← forallMetaTelescope type
  if tgtType.isAppOf `ML.Pattern then 
    let ir ← patternToIRM e 
    let ⟨mmpatt, env⟩ ← ir.toMMPatternM
    let pattInPrf := mmpatt.toMMInProof env
    return pattInPrf 
    -- return env
  else if tgtType.isAppOf `ML.EVar then 
    let ir ← patternToIRM e 
    let ⟨mmpatt, env⟩ ← ir.toMMPatternM
    let pattInPrf := mmpatt.toMMInProof env
    return pattInPrf 
    -- return env
  else 
    match e with 
    | .app e₁ e₂ => 
      let prf₂ ← proofToMM e₂ 
      let prf₁ ← proofToMM e₁
      return s! "{prf₂} {prf₁}"
    | .const id _ => 
      IO.println id 
      return toString id
    | _ => return ""
    
  
section 

      variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ χ θ : Pattern 𝕊} {x y : EVar}

      def test1 : Γ ⊢ φ[x ⇐ᵉ y] ⇒ φ[x ⇐ᵉ y] := ML.Proof.implSelf

      def test2 : Γ ⊢ ∃∃ x x := ML.Proof.existence

end 

def MLStmt.toMMProof (stmt : MLStmt) : MetaM MMProof := do 
  let label := stmt.name.map toString |>.getD "default-label"
  let ⟨conclusion, envConclusion⟩ ← (← patternToIRM stmt.conclusion).toMMPatternM
  let proof ← proofToMM stmt.proof.get! 
  return {
    label := label
    env := envConclusion.eraseDup
    proof := proof
    conclusion := conclusion
  }

#eval show MetaM Unit from do 
  let stmt ← parseMLStmt ``test2 
  let prf ← stmt.toMMProof 
  IO.println prf.toMM
  -- dbg_trace prf.env.metaVars 
  -- dbg_trace prf.env.floatings 
  -- dbg_trace prf.env.essentials
  -- dbg_trace prf.conclusion
  -- dbg_trace prf.conclusion

set_option pp.all true in 
#eval show MetaM _ from do 
  let stmt ← parseMLStmt ``test1
  let conclusion : IRPatt ← patternToIRM stmt.conclusion 
  let conclusion2 : IRPatt ← patternToIRM stmt.conclusion 
  let env ← proofToMM stmt.proof.get!
  let env2 ← proofToMM stmt.proof.get!
  -- IO.println env.metaVars  
  -- IO.println env2.metaVars 
  return env2

-- def toConclusion (stmt : MLStmt) : MetaM Env := do 
--   let conclusion : Expr := stmt.proof.get!
--   proofToMM conclusion


