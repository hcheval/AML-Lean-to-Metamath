import MatchingLogic

open ML Pattern Proof

namespace ML.Meta.Tests 





section Propositional 


  variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ χ : Pattern 𝕊} {x y : EVar}


end Propositional 





section Eta
  
  variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ χ : Pattern 𝕊} {x y : EVar}

  def etaModusPonensTest1 : Γ ⊢ φ → Γ ⊢ φ ⇒ ψ → Γ ⊢ ψ := modusPonens

  def etaModusPonensTest2 : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ → Γ ⊢ ψ := fun h₁ h₂ => modusPonens h₂ h₁ 

  def etaModusPonensTest3 (h₁ : Γ ⊢ φ) (h₂ : Γ ⊢ φ ⇒ ψ) : Γ ⊢ ψ := modusPonens h₁ h₂

  def etaModusPonensTest4 : Γ ⊢ φ → Γ ⊢ φ ⇒ ψ → Γ ⊢ ψ  := fun h₁ h₂ => modusPonens h₁ h₂

end Eta 




section Zeta 

  variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ χ : Pattern 𝕊} {x y : EVar}

  def testLet (h₁ : Γ ⊢ φ) (h₂ : Γ ⊢ φ ⇒ ψ) (h₃ : Γ ⊢ ψ ⇒ χ) : Γ ⊢ χ := 
    let l₁ : Γ ⊢ ψ := modusPonens h₁ h₂ 
    let l₂ : Γ ⊢ χ := modusPonens l₁ h₃ 
    l₂

end Zeta 




section BetaDelta  

    variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ χ : Pattern 𝕊} {x y : EVar}

    def testBeta1 (h : Γ ⊢ φ) : Γ ⊢ φ := id <| id <| id <| h 

    def testBeta2 (h : Γ ⊢ φ) : Γ ⊢ φ := (id ∘ id ∘ id) h

    def testBeta3 : Γ ⊢ φ → Γ ⊢ φ := id

end BetaDelta 




section Substitution 

  variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ χ : Pattern 𝕊} {x y : EVar}

  def substitutionModusPonens1 (h₁ : Γ ⊢ φ[x ⇐ᵉ y]) (h₂ : Γ ⊢ φ[x ⇐ᵉ y] ⇒ ψ[x ⇐ᵉ y]) : Γ ⊢ ψ[x ⇐ᵉ y] := 
    modusPonens h₁ h₂

  def substitutionModusPonens2 (h₁ : Γ ⊢ φ[x ⇐ᵉ ψ[x ⇐ᵉ y]]) : Γ ⊢ φ[x ⇐ᵉ ψ[x ⇐ᵉ y]] := h₁


  def substitutionModusPonens3 (h₁ : Γ ⊢ (φ ⇒ ψ)[x ⇐ᵉ y]) : Γ ⊢ (φ ⇒ ψ)[x ⇐ᵉ y] := h₁

end Substitution 




section Propositional 

  variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ χ : Pattern 𝕊} {x y : EVar}

  def modusPonensTest4 (h₁ : Γ ⊢ φ) (h₂ : Γ ⊢ φ ⇒ ψ) (h₃ : Γ ⊢ ψ ⇒ χ) := 
    modusPonens (modusPonens h₁ h₂) h₃

  def modusPonensTest6 (h₁ : Γ ⊢ φ ⇒ φ ⇒ φ) (h₂ : Γ ⊢ φ) : Γ ⊢ φ ⇒ φ := modusPonens h₂ h₁

end Propositional 



section FirstOrder

  variable {𝕊 : Type} {Γ : Premises 𝕊} {φ ψ χ : Pattern 𝕊} {x y : EVar}

  def modusPonensTest7 (h₁ : Γ ⊢ (∃∃ x x) ⇒ y) : Γ ⊢ y := modusPonens (existence) h₁

  
  def existQuanTest1 (sfi : (evar y).substitutableForEvarIn x φ) :
    Γ ⊢ (φ.substEvar x (.evar y) ⇒ ∃∃ x φ) := existQuan sfi

  def existGenTest1 (not_fv : ¬ψ.isFreeEvar x) : Γ ⊢ φ ⇒ ψ → Γ ⊢ (∃∃ x φ) ⇒ ψ := existGen not_fv

  def existenceTest1 : Γ ⊢ ∃∃ x x := existence


end FirstOrder 


def modusPonensTest8 : Γ ⊢ φ ⇒ ψ → Γ ⊢ φ → Γ ⊢ ψ := fun h₁ h₂ => (id modusPonens) h₂ h₁ 





section Transparency 


  @[irreducible]
  def testImpRelf : Γ ⊢ φ ⇒ φ := sorry 

  def testImpRelf' : Γ ⊢ φ ⇒ φ := testImpRelf

  def testImpRelf'' : Γ ⊢ φ ⇒ φ := testImpRelf'

  def testImpRelf''' (h : Γ ⊢ φ) : Γ ⊢ φ := modusPonens h testImpRelf'' 

end Transparency

