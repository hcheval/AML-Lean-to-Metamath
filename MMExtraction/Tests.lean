import MatchingLogic

open ML Pattern Proof

variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ χ : Pattern 𝕊} {x y : EVar}

def modusPonensTest0 : Γ ⊢ φ → Γ ⊢ φ ⇒ ψ → Γ ⊢ ψ := modusPonens

def modusPonensTest1 : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ → Γ ⊢ ψ := fun h₁ h₂ => modusPonens h₂ h₁ 

def modusPonensTest2 (h₁ : Γ ⊢ φ) (h₂ : Γ ⊢ φ ⇒ ψ) : Γ ⊢ ψ := modusPonens h₁ h₂

def modusPonensTest3 : Γ ⊢ φ → Γ ⊢ φ ⇒ ψ → Γ ⊢ ψ  := fun h₁ h₂ => modusPonens h₁ h₂

def modusPonensTest4 (h₁ : Γ ⊢ φ) (h₂ : Γ ⊢ φ ⇒ ψ) (h₃ : Γ ⊢ ψ ⇒ χ) := 
  modusPonens (modusPonens h₁ h₂) h₃

def modusPonensTest5 (h₁ : Γ ⊢ φ[x ⇐ᵉ y]) (h₂ : Γ ⊢ φ[x ⇐ᵉ y] ⇒ ψ[x ⇐ᵉ y]) : Γ ⊢ ψ[x ⇐ᵉ y] := 
  modusPonens h₁ h₂

def modusPonensTest6 (h₁ : Γ ⊢ φ ⇒ φ ⇒ φ) (h₂ : Γ ⊢ φ) : Γ ⊢ φ ⇒ φ := modusPonens h₂ h₁

def modusPonensTest7 (h₁ : Γ ⊢ (∃∃ x x) ⇒ y) : Γ ⊢ y := modusPonens (existence) h₁

def modusPonensTest8 : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ → Γ ⊢ ψ := fun h₁ h₂ => (id modusPonens) h₂ h₁ 

def existQuanTest1 (sfi : (evar y).substitutableForEvarIn x φ) :
  Γ ⊢ (φ.substEvar x (.evar y) ⇒ ∃∃ x φ) := existQuan sfi

def existGenTest1 (not_fv : ¬ψ.isFreeEvar x) : Γ ⊢ φ ⇒ ψ → Γ ⊢ (∃∃ x φ) ⇒ ψ := existGen not_fv

def existenceTest1 : Γ ⊢ ∃∃ x x := existence

@[irreducible]
def test1 (h₁ : Γ ⊢ ψ) : Γ ⊢ φ ⇒ ψ := modusPonens h₁ axK

@[irreducible]
def testImpRelf : Γ ⊢ φ ⇒ φ := sorry 

def testImpRelf' : Γ ⊢ φ ⇒ φ := testImpRelf

def testImpRelf'' : Γ ⊢ φ ⇒ φ := testImpRelf'

def testImpRelf''' (h : Γ ⊢ φ) : Γ ⊢ φ := modusPonens h testImpRelf'' 

def testLet (h₁ : Γ ⊢ φ) (h₂ : Γ ⊢ φ ⇒ ψ) (h₃ : Γ ⊢ ψ ⇒ χ) : Γ ⊢ χ := 
  let l₁ : Γ ⊢ ψ := modusPonens h₁ h₂ 
  let l₂ : Γ ⊢ χ := modusPonens l₁ h₃ 
  id l₂ 
