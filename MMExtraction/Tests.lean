import MatchingLogic

open ML Pattern Proof

namespace ML.Meta.Tests 





section Propositional 


  variable {๐ : Type} {ฮ : Premises ๐} {ฯ ฯ ฯ : Pattern ๐} {x y : EVar}


end Propositional 





section Eta
  
  variable {๐ : Type} {ฮ : Premises ๐} {ฯ ฯ ฯ : Pattern ๐} {x y : EVar}

  def etaModusPonensTest1 : ฮ โข ฯ โ ฮ โข ฯ โ ฯ โ ฮ โข ฯ := modusPonens

  def etaModusPonensTest2 : ฮ โข ฯ โ ฯ โ ฮ โข ฯ โ ฮ โข ฯ := fun hโ hโ => modusPonens hโ hโ 

  def etaModusPonensTest3 (hโ : ฮ โข ฯ) (hโ : ฮ โข ฯ โ ฯ) : ฮ โข ฯ := modusPonens hโ hโ

  def etaModusPonensTest4 : ฮ โข ฯ โ ฮ โข ฯ โ ฯ โ ฮ โข ฯ  := fun hโ hโ => modusPonens hโ hโ

end Eta 




section Zeta 

  variable {๐ : Type} {ฮ : Premises ๐} {ฯ ฯ ฯ : Pattern ๐} {x y : EVar}

  def testLet (hโ : ฮ โข ฯ) (hโ : ฮ โข ฯ โ ฯ) (hโ : ฮ โข ฯ โ ฯ) : ฮ โข ฯ := 
    let lโ : ฮ โข ฯ := modusPonens hโ hโ 
    let lโ : ฮ โข ฯ := modusPonens lโ hโ 
    lโ

end Zeta 




section BetaDelta  

    variable {๐ : Type} {ฮ : Premises ๐} {ฯ ฯ ฯ : Pattern ๐} {x y : EVar}

    def testBeta1 (h : ฮ โข ฯ) : ฮ โข ฯ := id <| id <| id <| h 

    def testBeta2 (h : ฮ โข ฯ) : ฮ โข ฯ := (id โ id โ id) h

    def testBeta3 : ฮ โข ฯ โ ฮ โข ฯ := id

end BetaDelta 




section Substitution 

  variable {๐ : Type} {ฮ : Premises ๐} {ฯ ฯ ฯ : Pattern ๐} {x y : EVar}

  def substitutionModusPonens1 (hโ : ฮ โข ฯ[x โแต y]) (hโ : ฮ โข ฯ[x โแต y] โ ฯ[x โแต y]) : ฮ โข ฯ[x โแต y] := 
    modusPonens hโ hโ

  def substitutionModusPonens2 (hโ : ฮ โข ฯ[x โแต ฯ[x โแต y]]) : ฮ โข ฯ[x โแต ฯ[x โแต y]] := hโ


  def substitutionModusPonens3 (hโ : ฮ โข (ฯ โ ฯ)[x โแต y]) : ฮ โข (ฯ โ ฯ)[x โแต y] := hโ

end Substitution 




section Propositional 

  variable {๐ : Type} {ฮ : Premises ๐} {ฯ ฯ ฯ : Pattern ๐} {x y : EVar}

  def modusPonensTest4 (hโ : ฮ โข ฯ) (hโ : ฮ โข ฯ โ ฯ) (hโ : ฮ โข ฯ โ ฯ) := 
    modusPonens (modusPonens hโ hโ) hโ

  def modusPonensTest6 (hโ : ฮ โข ฯ โ ฯ โ ฯ) (hโ : ฮ โข ฯ) : ฮ โข ฯ โ ฯ := modusPonens hโ hโ

end Propositional 



section FirstOrder

  variable {๐ : Type} {ฮ : Premises ๐} {ฯ ฯ ฯ : Pattern ๐} {x y : EVar}

  def modusPonensTest7 (hโ : ฮ โข (โโ x x) โ y) : ฮ โข y := modusPonens (existence) hโ

  
  def existQuanTest1 (sfi : (evar y).substitutableForEvarIn x ฯ) :
    ฮ โข (ฯ.substEvar x (.evar y) โ โโ x ฯ) := existQuan sfi

  def existGenTest1 (not_fv : ยฌฯ.isFreeEvar x) : ฮ โข ฯ โ ฯ โ ฮ โข (โโ x ฯ) โ ฯ := existGen not_fv

  def existenceTest1 : ฮ โข โโ x x := existence


end FirstOrder 


def modusPonensTest8 : ฮ โข ฯ โ ฯ โ ฮ โข ฯ โ ฮ โข ฯ := fun hโ hโ => (id modusPonens) hโ hโ 





section Transparency 


  @[irreducible]
  def testImpRelf : ฮ โข ฯ โ ฯ := sorry 

  def testImpRelf' : ฮ โข ฯ โ ฯ := testImpRelf

  def testImpRelf'' : ฮ โข ฯ โ ฯ := testImpRelf'

  def testImpRelf''' (h : ฮ โข ฯ) : ฮ โข ฯ := modusPonens h testImpRelf'' 

end Transparency

