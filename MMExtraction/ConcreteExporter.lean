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

variable [ToMMClaim 𝕊] [Repr 𝕊]



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




def Proof.toMMFile {𝕊 : Type} [ToMMClaim 𝕊] [DecidableEq 𝕊] [Repr 𝕊] {Γ : Premises 𝕊} {φ : Pattern 𝕊} 
  (proof : Proof Γ φ) 
  (label : String := "") 
  (pathToMatchingLogicPropositional : System.FilePath := "matching-logic-propositional.mm")
  (shapes : List <| Shape 𝕊 := Shape.standardPropositional)
  (premiseShapes : List <| Shape 𝕊 := [])
  : IO MMFile := 
do   
  let mut statementTheorems : Array String := #[]
  for statement in proof.statements shapes do 
    let statementTheorem ← MLITP.runProver statement 
    dbg_trace statementTheorem
    if !statementTheorems.contains statementTheorem then 
      statementTheorems := statementTheorems.push statementTheorem
    
  let mainThm : MMTheorem := {
    label := label 
    env := proof.createEnv 
    proof := proof.toMMProof shapes premiseShapes |>.get! 
    kind := .logical 
    conclusion := toMMClaim φ
  }  
  return {
    rawTheorems := statementTheorems.toList 
    theorems := [mainThm]
    includes := [pathToMatchingLogicPropositional]
  }

def extractProofToMM {𝕊 : Type} [ToMMClaim 𝕊] [DecidableEq 𝕊] [Repr 𝕊] {Γ : Premises 𝕊} {φ : Pattern 𝕊} 
  (proof : Proof Γ φ) 
  (label : String := "") 
  (pathToMatchingLogicPropositional : System.FilePath := "matching-logic-propositional.mm")
  (fname? : Option System.FilePath := none) 
  (shapes : List <| Shape 𝕊 := Shape.standardPropositional)
  (premiseShapes : List <| Shape 𝕊 := [])
  : IO Unit := do 
  let mmfile : MMFile ← Proof.toMMFile proof label pathToMatchingLogicPropositional shapes premiseShapes
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
-- #reduce @Proof.implSelf Empty ∅ ⊥ 

-- def thm' : ∅ ⊢ (⊥ ⇒ ⊥ : Pattern Empty) := .tautology <| by unfold_tautology!; intros; assumption
def thm' (φ ψ χ : Pattern Empty) : ∅ ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ χ) ⇒ (φ ⇒ χ) := Proof.tautology <| by 
  unfold_tautology!
  intros h h' 
  exact h' ∘ h

-- #eval thm' ⊥ ⊤ ⊥ |>.toMMFile

-- #eval @Proof.implSelf Empty ∅ ⊥ |>.statements 

-- #eval Proof.toMMFile /-(fname? := some "test-extracted.mm")-/ (@Proof.implSelf Empty ∅ ⊥) (shapes := [])

def extractProofToMMAndVerify {𝕊 : Type} [ToMMClaim 𝕊] [DecidableEq 𝕊] [Repr 𝕊] {Γ : Premises 𝕊} {φ : Pattern 𝕊} 
  (proof : Proof Γ φ)
  (pathToMetamath : System.FilePath)
  (fname : System.FilePath)
  (label : String := "")
  (pathToMatchingLogicPropositional : System.FilePath := "matching-logic-propositional.mm")
  (shapes : List <| Shape 𝕊 := Shape.standardPropositional)
  (premiseShapes : List <| Shape 𝕊 := [])
  : IO Bool := 
do 
  extractProofToMM proof label pathToMatchingLogicPropositional fname shapes premiseShapes 
  verifyFile pathToMetamath fname

-- def main : IO Unit := do 
--   let fname : System.FilePath := "test-extracted.mm"
--   extractProofToMM (@Proof.implSelf Empty ∅ ⊥) (label := "test") (fname? := some fname) 
--   if ← verifyFile "/home/horatiu/metamath-knife/metamath-knife" fname then 
--     IO.println "success"
--   else 
--     IO.println "failure"

-- #eval main




section TestsForBasicRules

def x₀ : EVar := ⟨0⟩

#eval (∃∃ x₀ x₀ : Pattern Empty).toMMProof.toMM

def existence₁ : ∅ ⊢ (∃∃ x₀ x₀ : Pattern Empty) := .existence

def implSelf₂ : ∅ ⊢ (∃∃ x₀ x₀ ⇒ ∃∃ x₀ x₀ : Pattern Empty) := .implSelf 

def modusPonens₁ : ∅ ⊢ (⊥ ⇒ ⊥ : Pattern Empty) := .implSelf -- because it uses `syllogism` which is two application of `modusPonens` 

def modusPonens₂ : ∅ ⊢ (∃∃ x₀ x₀ : Pattern Empty) := .modusPonens .existence .implSelf 

def implSelf₁ : ∅ ⊢ (⊤ : Pattern Empty) := .tautology <| by unfold_tautology! 

#eval modusPonens₁.statements (shapes := [])

#eval extractProofToMMAndVerify 
        (implSelf₁) 
        (fname := "test-extracted.mm") 
        (pathToMetamath := "/home/horatiu/metamath-knife/metamath-knife")
        (label := "test")
        -- (shapes := [])

end TestsForBasicRules 
