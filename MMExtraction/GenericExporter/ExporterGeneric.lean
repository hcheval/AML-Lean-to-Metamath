/-
  This is an alternative experimental design for the 
  metaprogramming based extractor.
-/

import Lean 
import MatchingLogic.Proof 
-- import MMExtraction.MMBuilder
import MMExtraction.Util
import MMExtraction.Tests

set_option autoImplicit false 

namespace ML.Meta 



open Lean Elab Term Meta Syntax


def getProofExpr (declName : Name) : MetaM Expr := do 
  let defnValue ← getDefnValue declName 
  let ⟨_, _, body⟩ ← lambdaMetaTelescope defnValue  
  let body ← etaExpand body 
  guard <| isNotDependentForall body
  let ⟨_, _, body⟩ ← lambdaMetaTelescope body 
  return body

section DataTypes 

  abbrev Pattern := String

  inductive MetavarInfo where 
  | evar 
  | pattern 
  | premise (claim : Pattern) 
  | irrelevant 
    deriving DecidableEq, Repr, Inhabited

  namespace MetavarInfo

    protected def MetavarInfo.toString (info : MetavarInfo) : String := 
      match info with 
      | evar => "evar"
      | pattern => "pattern"
      | premise claim => toString claim 
      | irrelevant => "irrelevant"

    instance : ToString MetavarInfo := ⟨MetavarInfo.toString⟩

  end MetavarInfo

  structure Metavar where 
    name : String 
    info : MetavarInfo
    deriving DecidableEq, Inhabited, Repr 

  namespace Metavar 

  end Metavar 


  inductive IRProof where
  | metavar : Metavar → IRProof
  | app (head : String) (args : List IRProof)
  | wrong (msg : String := "")
    deriving BEq, Inhabited, Repr


  namespace IRProof

    protected partial def toString (proof : IRProof) (nice : Bool := true) (indent : String := "") (metavarTypes : Bool := false) : String :=
    match proof with 
    | metavar ⟨name, info⟩ => 
      let typeStr := if metavarTypes then toString info else ""
      s! "{indent} {name} {typeStr}" ++ (if nice then ⟨[endl]⟩ else " ")
    | wrong msg => s! "{indent}(wrong {msg})"
    | app head args => 
      let argsStrs := args.map <| IRProof.toString (nice := nice) (indent := "  " ++ indent) (metavarTypes := metavarTypes)
      let argsStr := joinWith argsStrs ""
      argsStr ++ (indent ++ toString head) ++ (if nice then ⟨[endl]⟩ else " ")

    instance : ToString IRProof := ⟨IRProof.toString⟩

    partial def removeIrrelevant (proof : IRProof) : Option IRProof :=
      match proof with 
      | metavar ⟨name, info⟩ => if info == .irrelevant then none else some proof
      | wrong msg => some <| wrong msg 
      | app head args => 
        let args? := args.map removeIrrelevant
        some <| app head (args?.filter Option.isSome |>.map Option.get!)

    def exportMetavar (mv : Metavar) : IRProof :=
      match mv.info with 
      | .evar => app s! "{mv.name}-is-evar" []
      | .pattern => app s! "{mv.name}-is-pattern" [] 
      | .premise claim => .metavar ⟨mv.name, mv.info⟩
      | .irrelevant => app "" []

    def mkAppOfNameAndArity (name : String) (arity : ℕ) (argMapping : ℕ → ℕ := id) : List IRProof → IRProof := 
      fun args => app name (List.range arity |>.map (args[argMapping .]!))

    def getAppExporter? (head : String) : Option <| List IRProof → IRProof := 
      match head with 
      -- proof rules 
      | "ML.Proof.axK" => some <| mkAppOfNameAndArity "proof-rule-prop-1" 2
      | "ML.Proof.axS" => some <| mkAppOfNameAndArity "proof-rule-prop-2" 3
      | "ML.Proof.dne" => some <| mkAppOfNameAndArity "proof-rule-prop-2" 1
      | "ML.Proof.modusPonens" => some <| mkAppOfNameAndArity "proof-rule-mp" 4
      | "ML.Proof.existQuan" => some <| mkAppOfNameAndArity "proof-rule-exists" 4 
      | "ML.Proof.existGen" => some <| mkAppOfNameAndArity "proof-rule-gen" 5
      | "ML.Proof.existence" => some <| mkAppOfNameAndArity "proof-rule-existence" 1 
      | "ML.Proof.substitution" => some <| mkAppOfNameAndArity "proof-rule-substitution" 5
      | "ML.Proof.prefixpoint" => some <| mkAppOfNameAndArity "proof-rule-prefixpoint" 4 
      | "ML.Proof.knasterTarksi" => some <| mkAppOfNameAndArity "proof-rule-kt" 5
      -- pattern formation rules
      | "ML.Pattern.implication" => some <| mkAppOfNameAndArity "imp-is-pattern" 2 
      | "ML.Pattern.application" => some <| mkAppOfNameAndArity "app-is-pattern" 2 
      | "ML.Pattern.disjunction" => some <| mkAppOfNameAndArity "or-is-pattern" 2 
      | "ML.Pattern.conjunction" => some <| mkAppOfNameAndArity "and-is-pattern" 2 
      | "ML.Pattern.existential" => some <| mkAppOfNameAndArity "exists-is-pattern" 2 
      | "ML.Pattern.universal" => some <| mkAppOfNameAndArity "forall-is-pattern" 2 
      | "ML.Pattern.bottom" => some <| mkAppOfNameAndArity "bot-is-pattern" 2 
      | "ML.Pattern.evar" => some <| mkAppOfNameAndArity "evar-is-pattern" 1 
      | _ => none 
      
    partial def toPattern? (proof : IRProof) : String := 
      match proof with 
      | metavar ⟨name, info⟩ => name 
      | wrong msg => "wrong"
      | app head args => match head with 
        | "ML.Pattern.implication" => "( \\imp {toPattern? args[0]!} {toPattern? args[1]!} )"
        | "ML.Pattern.evar" => toPattern? args[0]!
        | _ => "wrong"

    partial def removeSubstEvar (proof : IRProof) : IRProof := 
      match proof with 
      | app head args => 
        if head == "ML.Pattern.substEvar" then 
          let args := args.map toPattern? 
          metavar ⟨("S" ++ joinWith args "-"), .pattern⟩   
        else 
          app head <| args.map removeSubstEvar
      | p@_ => p

    partial def mkExportable (proof : IRProof) : IRProof := 
      match proof with 
      | metavar mv => 
        exportMetavar mv
      | wrong msg => proof 
      | app head args => 
        if let some exportAs := getAppExporter? head then 
          exportAs <| args.map mkExportable
        else 
          wrong s! "no exporter found for {head}"

    partial def getMetavars (proof : IRProof) : List Metavar :=
      match proof with 
      | metavar ⟨name, info⟩ => [⟨name, info⟩]
      | wrong _ => []
      | app head args => 
        args.map getMetavars |>.join

    def isFloatingInfo (info : MetavarInfo) : Bool := 
      match info with | .pattern | .evar => true | _ => false 

    def isEssentialInfo (info : MetavarInfo) : Bool := 
      match info with | .premise _ => true | _ => false 

    def getFloatingMetavars (proof : IRProof) : List Metavar := 
      proof.getMetavars
        |>.filter fun ⟨_, info⟩ => isFloatingInfo info

    def getEssentialMetavars (proof : IRProof) : List Metavar := 
      proof.getMetavars
        |>.filter fun ⟨_, info⟩ => isEssentialInfo info

    def infoToFloatingLabel! (info : MetavarInfo) : String :=
      match info with 
      | .pattern => "pattern"
      | .evar => "evar"
      | _ => panic! s!"{info} is not floating"

    def infoToLeadingFloating! (info : MetavarInfo) : String :=
      match info with 
      | .pattern => "#Pattern"
      | .evar => "#EVar"
      | _ => panic! s!"{info} is not floating"

    def metavarToFloating (mv : Metavar) : String :=
      let label := s! "{mv.name}-is-{infoToFloatingLabel! mv.info} $."
      s! "{label} $f {infoToLeadingFloating! mv.info} {mv.name} $."

    inductive HypKind where 
    | floating | essential 
      deriving Inhabited, DecidableEq, Repr 

    structure Hypothesis where 
      label : String 
      kind : HypKind 
      stmt : String 
      deriving Inhabited, DecidableEq, Repr 

    def Hypothesis.toMM (hyp : Hypothesis) : String := 
      let kindStr := match hyp.kind with | .floating => "f" | .essential => "e"
      s! "{hyp.label} ${kindStr} {hyp.stmt} $."

    def metavarToHypothesis (mv : Metavar) : Option Hypothesis := 
      match mv.info with 
      | .pattern => some ⟨s! "{mv.name}-is-pattern", .floating, s! "#Pattern {mv.name}"⟩
      | .evar => some ⟨s! "{mv.name}-is-pattern", .floating, s! "#Pattern {mv.name}"⟩
      | .premise claim => some ⟨mv.name, .essential, s! "|- {claim}"⟩
      | .irrelevant => none 

end IRProof

end DataTypes

section Parsing 

  partial def asPatternInClaim (e : Expr) : String :=
    if e.isMVar then 
      toString e.mvarId!.name
    else if e.isAppOf `ML.Pattern.implication then 
      s! "( \\imp {asPatternInClaim e.getAppArgs[1]!} {asPatternInClaim e.getAppArgs[2]!} )"
    else if e.isAppOf `ML.Pattern.evar then 
      s! "{asPatternInClaim e.getAppArgs[0]!}"
    else if e.isAppOf `ML.Pattern.substEvar then 
      ("S" ++ joinWith [asPatternInClaim e.getAppArgs[1]!, asPatternInClaim e.getAppArgs[2]!, asPatternInClaim e.getAppArgs[3]!] "-")
    else 
      "error"

  def parseTypeAsMetavarInfo (type : Expr) : MetavarInfo := 
    if type.isConstOf `ML.EVar then 
      .evar 
    else if type.isAppOf `ML.Pattern then 
      .pattern 
    else if type.isAppOf `ML.Proof then 
      .premise <| asPatternInClaim type.getAppArgs[2]!
    else 
      .irrelevant

  partial def IRProof.fromExpr (e : Expr) : MetaM IRProof := do
      let e ← whnf e 
      if e.isMVar then 
        let info : MetavarInfo := parseTypeAsMetavarInfo (← inferType e)
        let name : String := toString e.mvarId!.name 
        return .metavar ⟨name, info⟩
      else if e.getAppFn.isConst then 
        let args : List IRProof ← e.getAppArgs.toList.mapM fromExpr 
        return .app (toString e.getAppFn.constName!) args
      else 
        return .wrong 

end Parsing 

section Exporting 

  partial def IRProof.toMM (proof : IRProof) : String := 
  match proof with 
  | metavar ⟨name, _⟩ => name 
  | wrong msg => "wrong"
  | app head args => 
    let argsStr := joinWith (args.map toMM) " "
    argsStr ++ " " ++ head

end Exporting 










  def prettifyMetavarUniqName (mv : Metavar) : String := 
    if let some idx := mv.name.extract ⟨"_uniq.5".length⟩ mv.name.endPos |>.toNat? then 
      s! "m{idx}"
    else 
      mv.name








structure ExportedProof where 
  label : String 
  metavars : List Metavar 
  floatings : List IRProof.Hypothesis  
  essentials : List IRProof.Hypothesis
  claim : String 
  proof : IRProof 

/-- Like `++` on strings, but adds a newline between the strings -/
infixl:50 "++n" => fun (str₁ str₂ : String) => String.append (String.append str₁ (String.mk [ML.Meta.endl])) str₂

def ExportedProof.toMM (proof : ExportedProof) : String := 
  let metavarsStr := joinWith (proof.metavars.map (fun ⟨name, _⟩ ↦ s! "$v {name} $.")) ⟨[endl]⟩
  let floatingsStr := joinWith (proof.floatings.map IRProof.Hypothesis.toMM) ⟨[endl]⟩
  let essentialsStr := joinWith (proof.essentials.map IRProof.Hypothesis.toMM) ⟨[endl]⟩
  let openingBracket := if !proof.essentials.isEmpty then s! "{endl}" ++ "${" else ""
  let closingBracket := if !proof.essentials.isEmpty then ⟨[endl]⟩ ++ "$}" else ""
  s! "
{metavarsStr}
{floatingsStr} {openingBracket}
{essentialsStr} 
{proof.label} $p {proof.claim} $=
{proof.proof.toMM} $. {closingBracket}
"
  -- metavarsStr ++n floatingsStr ++n essentialsStr ++n s! "{proof.label} $p {proof.claim} $= {endl}" ++n proof.proof.toMM ++n "$."

def exportProof (declName : Name) : MetaM ExportedProof := do 
  let proof ← getProofExpr declName 
  let type ← inferType proof 
  let irproof ← IRProof.fromExpr proof
  let withAllMetavars := irproof.removeIrrelevant.get!.removeSubstEvar 
  return {
    label := toString declName 
    metavars := withAllMetavars.getMetavars.eraseDup
    floatings := withAllMetavars.getMetavars.map IRProof.metavarToHypothesis 
      |>.filter Option.isSome 
      |>.map Option.get!
      |>.filter (fun hyp ↦ hyp.kind == .floating)
      |>.eraseDup 
    essentials := withAllMetavars.getEssentialMetavars.map IRProof.metavarToHypothesis 
      |>.filter Option.isSome 
      |>.map Option.get! 
      |>.filter (fun hyp ↦ hyp.kind == .essential)
      |>.eraseDup
    claim := asPatternInClaim type.getAppArgs[2]!
    proof := withAllMetavars.mkExportable
  }

def test (declName : Name) : MetaM Unit := do 
  let exported ← exportProof declName
  -- IO.println exported.metavars 
  -- IO.println <| exported.floatings.map IRProof.Hypothesis.toMM
  -- IO.println <| exported.essentials.map IRProof.Hypothesis.toMM   
  -- IO.println exported.claim    
  IO.println exported.toMM  



