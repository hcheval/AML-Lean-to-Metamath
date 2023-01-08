import MatchingLogic 
import MMExtraction.ConcreteExporter.ToMMProof 
import MMExtraction.ConcreteExporter.Freshness
import MMExtraction.MMBuilder 

set_option autoImplicit false

namespace ML 

open ML.Meta

variable {𝕊 : Type} [ToMMClaim 𝕊]

inductive Substitution (𝕊 : Type) where 
| varSame (xX : Var) (φ₀ : Pattern 𝕊) 
| varDiff (xX : Var) (φ₀ : Pattern 𝕊) (yY : Var)
| symbol (var : Var) (substituent : Pattern 𝕊) (σ : 𝕊)
| bot (var : Var) (substituent : Pattern 𝕊) 
| imp (var : Var) (substituent : Pattern 𝕊) (φ₁ φ₂ : Pattern 𝕊) (s₁ s₂ : Substitution 𝕊) 
| app (var : Var) (substituent : Pattern 𝕊) (φ₁ φ₂ : Pattern 𝕊) (s₁ s₂ : Substitution 𝕊) 
| existShadowed (substituent : Pattern 𝕊) (x : EVar) (φ : Pattern 𝕊)
| exist (var : Var) (substituent : Pattern 𝕊) (x : EVar) (φ : Pattern 𝕊) (s : Substitution 𝕊)
| muShadowed (substituent : Pattern 𝕊) (X : SVar) (φ : Pattern 𝕊)
| mu (var : Var) (substituent : Pattern 𝕊) (X : SVar) (φ : Pattern 𝕊) (s : Substitution 𝕊)
| identity (xX : Var) (φ₀ : Pattern 𝕊)
| fresh (xX : Var) (substituent : Pattern 𝕊) (target : Pattern 𝕊) (hfresh : Fresh xX target)



/--
  `autoSubstitution? xX ψ φ` produces a Metamath proof that `φ[xX ⇐ ψ]` is the free substitution of 
  `xX` by `ψ` in `φ`, or returns `none` if such a substitution is not free. 

  Unlinke the Metamath definition, `autoSubstitution?` does **not** perform α-renaming to make 
  all substitutions capture-avoiding. One should do this in Lean **before** attemtping to extract the proof.
-/
def autoSubstitution? (var : Var) (substituent : Pattern 𝕊) (target : Pattern 𝕊) : Option <| Substitution 𝕊 := 
do 
  if let some fresh := autoFresh var target then 
    return .fresh var substituent target fresh

  let identity? : Option <| Substitution 𝕊 := 
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
  | .symbol σ => 
    return .symbol var substituent σ
  | ⊥ => 
    return .bot var substituent 
  | φ₁ ⇒ φ₂ => 
    let s₁ ← autoSubstitution? var target φ₁ 
    let s₂ ← autoSubstitution? var target φ₂
    return .imp var substituent φ₁ φ₂ s₁ s₂
  | φ₁ ⬝ φ₂ => 
    let s₁ ← autoSubstitution? var target φ₁ 
    let s₂ ← autoSubstitution? var target φ₂
    return .imp var substituent φ₁ φ₂ s₁ s₂
  | ∃∃ x φ => 
    if var = .inl x then 
      return .existShadowed substituent x φ
    else if .inl x ∉ φ.allVars then 
      let s ← autoSubstitution? var target φ
      return .exist var substituent x φ s
    else none 
  | μ X φ => 
    if var = .inr X then 
      return .muShadowed substituent X φ
    else if .inr X ∉ φ.allVars then 
      let s ← autoSubstitution? var target φ
      return .mu var substituent X φ s
    else none 
  | _ => none 

/-
  FOR ME: The earlier a floating is declared, the higher it needs to be in the argument stack,
  meaning the more at the beginning of the `MMProof.app` arguments
-/

protected def Substitution.toMMProof : Substitution 𝕊 → MMProof 
  | varSame var substituent => 
    .app "substitution-var-same" [toMMProof substituent, toMMProof var]
  | varDiff var substituent yY => 
    .app "substitution-var-diff" [toMMProof substituent, toMMProof var, toMMProof yY]
  | symbol var substituent σ => 
    .app "substitution-var-symbol" [toMMProof substituent, toMMProof var, toMMProof σ]
  | bot var substituent => 
    .app "substitution-bot" [toMMProof substituent, toMMProof var]
  | imp var substituent φ₁ φ₂ s₁ s₂ => 
    .app "substitution-imp" [toMMProof substituent, toMMProof (φ₁[var ⇐ substituent]), toMMProof (φ₂[var ⇐ substituent]), toMMProof φ₁, toMMProof φ₂, toMMProof var]
  | app var substituent φ₁ φ₂ s₁ s₂ => 
    .app "substitution-app" [toMMProof substituent, toMMProof (φ₁[var ⇐ substituent]), toMMProof (φ₂[var ⇐ substituent]), toMMProof φ₁, toMMProof φ₂, toMMProof var]
  | existShadowed substituent x φ =>   
    .app "substitution-exists-shadowed" [toMMProof substituent, toMMProof φ, toMMProof x]