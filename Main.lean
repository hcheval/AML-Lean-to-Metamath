import MMExtraction.MLParser 

set_option autoImplicit false 

open Lean 
open ML Meta

section Tests 

  variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ χ : Pattern 𝕊} {x y : EVar}

  def modusPonensTest0 : Γ ⊢ φ → Γ ⊢ φ ⇒ ψ → Γ ⊢ ψ := Proof.modusPonens

  def modusPonensTest1 : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ → Γ ⊢ ψ := fun h₁ h₂ => Proof.modusPonens h₂ h₁ 

  def modusPonensTest2 (h₁ : Γ ⊢ φ) (h₂ : Γ ⊢ φ ⇒ ψ) : Γ ⊢ ψ := Proof.modusPonens h₁ h₂

  def modusPonensTest3 : Γ ⊢ φ → Γ ⊢ φ ⇒ ψ → Γ ⊢ ψ  := fun h₁ h₂ => Proof.modusPonens h₁ h₂

  def modusPonensTest4 (h₁ : Γ ⊢ φ) (h₂ : Γ ⊢ φ ⇒ ψ) (h₃ : Γ ⊢ ψ ⇒ χ) := 
    Proof.modusPonens (Proof.modusPonens h₁ h₂) h₃

  def modusPonensTest5 (h₁ : Γ ⊢ φ[x ⇐ᵉ y]) (h₂ : Γ ⊢ φ[x ⇐ᵉ y] ⇒ ψ[x ⇐ᵉ y]) : Γ ⊢ ψ[x ⇐ᵉ y] := 
    Proof.modusPonens h₁ h₂

  def existQuanTest1 (sfi : (Pattern.evar y).substitutableForEvarIn x φ) :
    Γ ⊢ (φ.substEvar x (.evar y) ⇒ ∃∃ x φ) := Proof.existQuan sfi

  def existGenTest1 (not_fv : ¬ψ.isFreeEvar x) : Γ ⊢ φ ⇒ ψ → Γ ⊢ (∃∃ x φ) ⇒ ψ := Proof.existGen not_fv

  def existenceTest1 : Γ ⊢ ∃∃ x x := Proof.existence

  @[irreducible]
  def test1 (h₁ : Γ ⊢ ψ) : Γ ⊢ φ ⇒ ψ := Proof.modusPonens h₁ Proof.axK

  @[mm_extern "imp-reflexivity", irreducible]
  def testImpRelf : Γ ⊢ φ ⇒ φ := sorry 

  def testImpRelf' : Γ ⊢ φ ⇒ φ := testImpRelf

  def testImpRelf'' : Γ ⊢ φ ⇒ φ := testImpRelf'

  def testImpRelf''' (h : Γ ⊢ φ) : Γ ⊢ φ := Proof.modusPonens h testImpRelf'' 

end Tests

-- def exportToMMAs (declName : Name) : CoreM (Option String) := do 
--   return mmExternAttr.getParam? (← getEnv) declName


-- because typing backslash and then n is remarkably annoying

def println {α : Type} [ToString α] (newlines : ℕ) (a : α) : IO Unit := do 
  IO.println <| toString a
  for _ in [1:newlines] do 
    IO.println ""

-- attribute [irreducible] testImpRelf
#eval show MetaM Unit from do 
  let thm ← parseMLTheorem ``modusPonensTest4
  println 2 thm.proof
  -- println 2 name.get!
  let conclusion ← patternToIRM thm.conclusion 
  let proof ← proofToIRStructured thm.proof 
  println 2 thm.name.get! 
  println 2 conclusion 
  println 2 proof.createEnv.eraseDup 
  println 2 proof.toMMString

def main : IO Unit := do 
  IO.println "hello"

#eval main 