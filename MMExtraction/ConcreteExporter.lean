import MatchingLogic 
import MMExtraction.MMBuilder
import MMExtraction.Attributes
import MMExtraction.ConcreteExporter.ToMMClaim
import MMExtraction.ConcreteExporter.ToMMProofProof 
import MMExtraction.ConcreteExporter.CreateEnv 

set_option autoImplicit false 

namespace ML 

open ML.Meta 

@[for_matching_logic]
instance : ToString EVar where 
  toString := toString ∘ EVar.val

@[for_matching_logic]
instance : ToString SVar where 
  toString := toString ∘ SVar.val








variable {𝕊 : Type} 

variable [ToMMClaim 𝕊]



def Tests.patternsAsClaims : Array (Pattern Empty × String) := #[
  ⟨⊥, "bot"⟩,
  ⟨.evar ⟨4⟩, "x4"⟩,
  ⟨.svar ⟨4⟩, "X4"⟩,
  ⟨⊥ ⇒ ⊥, "( imp bot bot )"⟩,
  ⟨⊥ ⇒ ⊥ ⇒ ⊥, "( imp bot ( imp bot bot ) )"⟩,
  ⟨(⊥ ⇒ ⊥) ⇒ ⊥, "( imp ( imp bot bot ) bot )"⟩,
  ⟨⊥ ⬝ ⊥, "( app bot bot )"⟩,
  ⟨⊥ ⬝ ⊥ ⬝ ⊥,"( app ( app bot bot ) bot )"⟩,
  ⟨⊥ ⬝ (⊥ ⬝ ⊥), "( app bot ( app bot bot ) )"⟩,
  ⟨∃∃ ⟨3⟩ (.evar ⟨3⟩), "( exists x3 x3 )"⟩
]

deriving instance Repr for EVar 
deriving instance Repr for SVar
deriving instance Repr for Pattern 
deriving instance Repr for Empty 







/- Freshness. Done, modulo bug fixes. -/

section Freshness 

end Freshness

















def Proof.toMMFile {𝕊 : Type} [ToMMClaim 𝕊] [DecidableEq 𝕊] {Γ : Premises 𝕊} {φ : Pattern 𝕊} (proof : Proof Γ φ) 
  (label : String := "") 
  (pathToMatchingLogic : System.FilePath := "matching-logic.mm") 
  (pathToMatchingLogicPrelude : System.FilePath := "matching-logic-prelude.mm")
  (pathToMatchingLogicPropositional : System.FilePath := "matching-logic-propositional.mm")
  (shapes : List <| Shape 𝕊 := [])
  (premiseShapes : List <| Shape 𝕊 := [])
  : MMFile := 
Id.run do 
  let mmproof := proof.toMMProof shapes premiseShapes |>.get! 
  let mmtheorem : MMTheorem := {
    conclusion := toMMClaim φ
    proof := mmproof 
    label := label 
    env := proof.createEnv 
  }
  return .fromMMTheorems [mmtheorem] [pathToMatchingLogic, pathToMatchingLogicPrelude, pathToMatchingLogicPropositional]




def extractProofToMM {𝕊 : Type} [ToMMClaim 𝕊] [DecidableEq 𝕊] {Γ : Premises 𝕊} {φ : Pattern 𝕊} (proof : Proof Γ φ) 
  (label : String := "") 
  (pathToMatchingLogic : System.FilePath := "matching-logic.mm")
  (fname? : Option System.FilePath := none) 
  : IO Unit := do 
  let mmfile : MMFile := Proof.toMMFile proof label pathToMatchingLogic
  if let some fname := fname? then 
    mmfile.writeToFile fname 
  else 
    IO.println mmfile.toMM 


def verifyFile (pathToMetamath : System.FilePath) (fname : System.FilePath) : IO Bool := do 
  let output ← IO.Process.output {
    cmd := toString pathToMetamath
    args := #["--verify", toString fname]
  }
  return output.exitCode == 0  




def main : IO Unit := do 
  let fname : System.FilePath := "test-extracted.mm"
  extractProofToMM (@ML.Proof.existence Empty ∅ (⟨0⟩)) (label := "existence-test") (fname? := some fname) 
  if ← verifyFile "/home/horatiu/metamath-knife/metamath-knife" fname then 
    IO.println "success"
  else 
    IO.println "failure"

#eval main