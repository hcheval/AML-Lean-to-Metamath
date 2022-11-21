import Lean
import MatchingLogic.Proof 
import MMExtraction.MMBuilder
import MMExtraction.IntermediateRepresentation

open Lean Elab Term Meta Syntax 

set_option autoImplicit false 

namespace ML.Meta 


/--
  Stores a "parsed" Matching Logic statement with fields:
  * `name : Option Name` 
  * `premises : List Expr` 
  * `conclusion : Expr` 
  * `proof : Option Expr`.
  The `name` and `premises` fields are optional.
-/
structure MLTheorem where 
  label : Option Name := none 
  /-
    premises we care about are the following:
    * ml-premises 
    * substitutability 
    * (not) free-variableness 
  -/
  premises : List Expr := []
  conclusion : Expr 
  proof : Expr 
  deriving Repr

/--
  `isOfTypeMLProof e` returns `true` iff the type of `e` is of the form `Γ ⊢ φ`.
-/
def isOfTypeMLProof : Expr → MetaM Bool := 
  fun e => do return Expr.isAppOf (← inferType e) `ML.Proof


-- TO REMEMBER: meta-telescopes should only be called once! A subsequent call will give fresh mvars, thus breaking coherence
/--
  Given a Matching Logic theorem `def id : Γ ⊢ φ₁ → ... → Γ ⊢ φₙ → Γ ⊢ ψ := prf`,
  `parseMLStmt id` returns a `MLTheorem` with 
  * `conclusion := ψ`
  * `proof := prf`
  * `premises := [φ₁, ..., φₙ]` 
  * `name := id`.
-/
def parseMLTheorem (id : Name) : MetaM MLTheorem := do 
  match (← getEnv).find? id with 
  | ConstantInfo.defnInfo { value := v, .. } =>   
    let v ← etaExpand v 
    let ⟨_, _, body⟩ ← lambdaMetaTelescope v 
    let body ← whnf body 
    let type ← inferType body 
    -- should check that `type` is non-dependent before telescoping 
    let ⟨_, _, targetType⟩ ← forallMetaTelescope type 
    -- should check that `targetType` is an application of `Proof` before proceeding 
    return { 
      conclusion := targetType.getAppArgs[2]!
      proof := body 
      -- premises := (← args.toList.mapM inferType).filter <| (Expr.isAppOf . `ML.Proof)
      label := toString id
    }
  | none => throwError m! "Unknown identifier {id}"
  | _ => throwError "{id} is not a definition"







  

section Tests 

  variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ : Pattern 𝕊} {x y : EVar}

  def modusPonensTest0 : Γ ⊢ φ → Γ ⊢ φ ⇒ ψ → Γ ⊢ ψ := Proof.modusPonens

  def modusPonensTest1 : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ → Γ ⊢ ψ := fun h₁ h₂ => Proof.modusPonens h₂ h₁ 

  def modusPonensTest2 (h₁ : Γ ⊢ φ) (h₂ : Γ ⊢ φ ⇒ ψ) : Γ ⊢ ψ := Proof.modusPonens h₁ h₂

  def modusPonensTest3 : Γ ⊢ φ → Γ ⊢ φ ⇒ ψ → Γ ⊢ ψ  := fun h₁ h₂ => Proof.modusPonens h₁ h₂

  def existQuanTest1 (sfi : (Pattern.evar y).substitutableForEvarIn x φ) :
    Γ ⊢ (φ.substEvar x (.evar y) ⇒ ∃∃ x φ) := Proof.existQuan sfi

  def existGenTest1 (not_fv : ¬ψ.isFreeEvar x) : Γ ⊢ φ ⇒ ψ → Γ ⊢ (∃∃ x φ) ⇒ ψ := Proof.existGen not_fv

  def existenceTest1 : Γ ⊢ ∃∃ x x := Proof.existence


end Tests


-- because typing backslash and then n is remarkably annoying
def endl : Char := ⟨10, by simp⟩

def println {α : Type} [ToString α] (newlines : ℕ) (a : α) : IO Unit := do 
  IO.println <| toString a
  for _ in [1:newlines] do 
    IO.println ""



#eval show MetaM Unit from do 
  let ⟨name, premises, conclusion, proof⟩ ← parseMLTheorem ``existGenTest1
  println 2 "After parsing:"
  -- println 2 name.get! 
  -- println 2 conclusion
  println 2 proof 
  IO.println <| ← proofToIRStructured proof


-- e : α → β 
-- fun x : α => e x 



#eval show MetaM Unit from do       
  -- parsing 
  let ⟨name, premises, conclusion, proof⟩ ← parseMLTheorem ``modusPonensTest2
  println 2 "After parsing:"
  println 2 name.get! 
  println 2 conclusion
  println 2 proof 
  -- #exit
  println 2 "________________________________"
  println 2 "After passing patterns to ir:"
  let conclusion ← patternToIRM conclusion
  let ⟨proof, proofEnv⟩ ← proofToIRUnstructured proof 
  println 2 name.get! 
  println 2 conclusion
  println 2 proof 
  println 2 proofEnv.metavars 
  println 2 proofEnv.floatings 
  println 2 proofEnv.essentials 
  println 2 "________________________________"
  println 2 "After passing conclusion to mm"
  let ⟨conclusion, env⟩ := conclusion.toMMPatt
  let env := env.eraseDup
  println 2 name.get! 
  println 1 env.metavars
  println 1 env.floatings
  println 1 env.essentials
  println 2 conclusion
  println 2 proof 
  println 2 "________________________________"
  println 2 "After passing proof to mm"
  let proof := proof.toMMProofUnstructured 
  println 2 name.get! 
  println 1 env.metavars
  println 1 env.floatings
  println 1 env.essentials
  println 2 conclusion
  println 2 proof 
  println 2 "________________________________"
  println 2 "After passing proof to string"
  let proof : List String := proof.map 
    fun token => match token with 
    | .inl patt => patt.toMMInProof env 
    | .inr name => name 
  println 2 name.get! 
  let env := env.merge proofEnv
  println 1 env.metavars
  println 1 env.floatings
  println 1 env.essentials
  println 2 conclusion
  println 2 proof 

  /-
    parse → irproof → irpoof × env → 
  -/

  