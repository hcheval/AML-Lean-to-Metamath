import MatchingLogic 
import MMExtraction.ConcreteExporter.ToMMProof 
import MMExtraction.ConcreteExporter.Freshness
import MMExtraction.MMBuilder 

set_option autoImplicit false

namespace ML 

open ML.Meta

variable {š : Type} [ToMMClaim š]

inductive Substitution (š : Type) where 
| varSame (xX : Var) (Ļā : Pattern š) 
| varDiff (xX : Var) (Ļā : Pattern š) (yY : Var)
| symbol (var : Var) (substituent : Pattern š) (Ļ : š)
| bot (var : Var) (substituent : Pattern š) 
| imp (var : Var) (substituent : Pattern š) (Ļā Ļā : Pattern š) (sā sā : Substitution š) 
| app (var : Var) (substituent : Pattern š) (Ļā Ļā : Pattern š) (sā sā : Substitution š) 
| existShadowed (substituent : Pattern š) (x : EVar) (Ļ : Pattern š)
| exist (var : Var) (substituent : Pattern š) (x : EVar) (Ļ : Pattern š) (s : Substitution š)
| muShadowed (substituent : Pattern š) (X : SVar) (Ļ : Pattern š)
| mu (var : Var) (substituent : Pattern š) (X : SVar) (Ļ : Pattern š) (s : Substitution š)
| identity (xX : Var) (Ļā : Pattern š)
| fresh (xX : Var) (substituent : Pattern š) (target : Pattern š) (hfresh : Fresh xX target)



/--
  `autoSubstitution? xX Ļ Ļ` produces a Metamath proof that `Ļ[xX ā Ļ]` is the free substitution of 
  `xX` by `Ļ` in `Ļ`, or returns `none` if such a substitution is not free. 

  Unlinke the Metamath definition, `autoSubstitution?` does **not** perform Ī±-renaming to make 
  all substitutions capture-avoiding. One should do this in Lean **before** attemtping to extract the proof.
-/
def autoSubstitution? (var : Var) (substituent : Pattern š) (target : Pattern š) : Option <| Substitution š := 
do 
  if let some fresh := autoFresh var target then 
    return .fresh var substituent target fresh

  let identity? : Option <| Substitution š := 
    do match var, substituent with 
    | .inl x, .evar y => if x = y then return .identity (.inl x) target else none 
    | .inr X, .svar Y => if X = Y then return .identity (.inr X) target else none 
    | _, _ => none 
  if let some identity := identity? then 
    return identity 

  match target with 
  | .evar x =>
    if var = .inl x then 
      return .varSame var substituent 
    else 
      return .varDiff var substituent (.inl x) 
  | .symbol Ļ => 
    return .symbol var substituent Ļ
  | ā„ => 
    return .bot var substituent 
  | Ļā ā Ļā => 
    let sā ā autoSubstitution? var target Ļā 
    let sā ā autoSubstitution? var target Ļā
    return .imp var substituent Ļā Ļā sā sā
  | Ļā ā¬ Ļā => 
    let sā ā autoSubstitution? var target Ļā 
    let sā ā autoSubstitution? var target Ļā
    return .imp var substituent Ļā Ļā sā sā
  | āā x Ļ => 
    if var = .inl x then 
      return .existShadowed substituent x Ļ
    else if .inl x ā Ļ.allVars then 
      let s ā autoSubstitution? var target Ļ
      return .exist var substituent x Ļ s
    else none 
  | Ī¼ X Ļ => 
    if var = .inr X then 
      return .muShadowed substituent X Ļ
    else if .inr X ā Ļ.allVars then 
      let s ā autoSubstitution? var target Ļ
      return .mu var substituent X Ļ s
    else none 
  | _ => none 

/-
  FOR ME: The earlier a floating is declared, the higher it needs to be in the argument stack,
  meaning the more at the beginning of the `MMProof.app` arguments
-/

protected def Substitution.toMMProof : Substitution š ā MMProof 
  | varSame var substituent => 
    .app "substitution-var-same" [toMMProof substituent, toMMProof var]
  | varDiff var substituent yY => 
    .app "substitution-var-diff" [toMMProof substituent, toMMProof var, toMMProof yY]
  | symbol var substituent Ļ => 
    .app "substitution-var-symbol" [toMMProof substituent, toMMProof var, toMMProof Ļ]
  | bot var substituent => 
    .app "substitution-bot" [toMMProof substituent, toMMProof var]
  | imp var substituent Ļā Ļā sā sā => 
    .app "substitution-imp" [toMMProof substituent, toMMProof (Ļā[var ā substituent]), toMMProof (Ļā[var ā substituent]), toMMProof Ļā, toMMProof Ļā, toMMProof var]
  | app var substituent Ļā Ļā sā sā => 
    .app "substitution-app" [toMMProof substituent, toMMProof (Ļā[var ā substituent]), toMMProof (Ļā[var ā substituent]), toMMProof Ļā, toMMProof Ļā, toMMProof var]
  | existShadowed substituent x Ļ =>   
    .app "substitution-exists-shadowed" [toMMProof substituent, toMMProof Ļ, toMMProof x]