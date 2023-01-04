import MatchingLogic 
import MMExtraction.MMBuilder 
import MMExtraction.Attributes
import MMExtraction.ConcreteExporter.ToMMClaim
import MMExtraction.ConcreteExporter.Var
import MMExtraction.ConcreteExporter.ToLabel
import MMExtraction.ConcreteExporter.ToMMProof
import MMExtraction.ConcreteExporter.Shape

namespace ML 

open ML.Meta

variable {𝕊 : Type} [ToMMClaim 𝕊] 

@[for_matching_logic]
def Pattern.symbols : Pattern 𝕊 → List 𝕊 
| symbol σ => [σ]
| φ ⇒ ψ | φ ⬝ ψ => φ.symbols ++ ψ.symbols 
| ∃∃ _ φ | μ _ φ => φ.symbols 
| evar _ | svar _ | ⊥ => []

@[for_matching_logic]
def AppContext.patterns := @AppContext.toList 

def Pattern.createEnv : Pattern 𝕊 → Env := fun φ ↦ Id.run do 
  let mut newenv : Env := {}
  for symbol in φ.symbols do 
    newenv := newenv.addSymbol <| toMMClaim symbol 
  for evar in φ.evars do 
    newenv := newenv.addElementVar evar.toMMClaim
  for svar in φ.svars do 
    newenv := newenv.addSetVar svar.toMMClaim 
  return newenv 


def Proof.symbols {Γ : Premises 𝕊} {φ : Pattern 𝕊} (proof : Proof Γ φ) : List 𝕊 :=
  match proof with 
  | @tautology _ _ φ _ => φ.symbols
  | @premise _ _ φ _ hmem => φ.symbols
  | @modusPonens _ _ φ ψ h₁ h₂ => h₁.symbols ++ h₂.symbols 
  | @existQuan _ _ φ x y sfi => φ.symbols
  | @existGen _ _ φ ψ x nfv h => h.symbols
  | @existence _ _ x => []
  | @propagationBottomLeft _ _ c => c.symbols
  | @propagationBottomRight _ _ c => c.symbols
  | @propagationDisjLeft _ _ φ ψ c => φ.symbols ++ ψ.symbols ++ c.symbols
  | @propagationDisjRight _ _ φ ψ c => φ.symbols ++ ψ.symbols ++ c.symbols 
  | @propagationExistLeft _ _ φ x c nfv => φ.symbols ++ c.symbols
  | @propagationExistRight _ _ φ x c nfv => φ.symbols ++ c.symbols 
  | @framingLeft _ _ φ ψ χ h => h.symbols ++ χ.symbols 
  | @framingRight _ _ φ ψ χ h => h.symbols ++ χ.symbols 
  | @substitution _ _ φ ψ X sfi h => h.symbols ++ ψ.symbols 
  | @prefixpoint _ _ φ X sfi pos => φ.symbols
  | @knasterTarski _ _ φ ψ X sfi h => h.symbols
  | @Proof.singleton _ _ C₁ C₂ x φ => φ.symbols ++ (C₁[⊥].symbols) ++ (C₂[⊥].symbols)

def Proof.allEVars {Γ : Premises 𝕊} {φ : Pattern 𝕊} (proof : Proof Γ φ) : List EVar :=
  match proof with 
  | @tautology _ _ φ _ => φ.allEVars
  | @premise _ _ φ _ hmem => φ.allEVars
  | @modusPonens _ _ φ ψ h₁ h₂ => h₁.allEVars ++ h₂.allEVars 
  | @existQuan _ _ φ x y sfi => x :: y :: φ.allEVars
  | @existGen _ _ φ ψ x nfv h => x :: h.allEVars
  | @existence _ _ x => [x]
  | @propagationBottomLeft _ _ c => c.allEVars
  | @propagationBottomRight _ _ c => c.allEVars
  | @propagationDisjLeft _ _ φ ψ c => φ.allEVars ++ ψ.allEVars ++ c.allEVars
  | @propagationDisjRight _ _ φ ψ c => φ.allEVars ++ ψ.allEVars ++ c.allEVars 
  | @propagationExistLeft _ _ φ x c nfv => x :: φ.allEVars ++ c.allEVars
  | @propagationExistRight _ _ φ x c nfv => x :: φ.allEVars ++ c.allEVars 
  | @framingLeft _ _ φ ψ χ h => h.allEVars ++ χ.allEVars 
  | @framingRight _ _ φ ψ χ h => h.allEVars ++ χ.allEVars 
  | @substitution _ _ φ ψ X sfi h => h.allEVars ++ ψ.allEVars 
  | @prefixpoint _ _ φ X sfi pos => φ.allEVars
  | @knasterTarski _ _ φ ψ X sfi h => h.allEVars
  | @Proof.singleton _ _ C₁ C₂ x φ => φ.allEVars ++ (C₁[⊥].allEVars) ++ (C₂[⊥].allEVars)

def Proof.allSVars {Γ : Premises 𝕊} {φ : Pattern 𝕊} (proof : Proof Γ φ) : List SVar :=
  match proof with 
  | @tautology _ _ φ _ => φ.allSVars
  | @premise _ _ φ _ hmem => φ.allSVars
  | @modusPonens _ _ φ ψ h₁ h₂ => h₁.allSVars ++ h₂.allSVars 
  | @existQuan _ _ φ x y sfi => φ.allSVars
  | @existGen _ _ φ ψ x nfv h => h.allSVars
  | @existence _ _ x => []
  | @propagationBottomLeft _ _ c => c.allSVars
  | @propagationBottomRight _ _ c => c.allSVars
  | @propagationDisjLeft _ _ φ ψ c => φ.allSVars ++ ψ.allSVars ++ c.allSVars
  | @propagationDisjRight _ _ φ ψ c => φ.allSVars ++ ψ.allSVars ++ c.allSVars 
  | @propagationExistLeft _ _ φ x c nfv => φ.allSVars ++ c.allSVars
  | @propagationExistRight _ _ φ x c nfv => φ.allSVars ++ c.allSVars 
  | @framingLeft _ _ φ ψ χ h => h.allSVars ++ χ.allSVars 
  | @framingRight _ _ φ ψ χ h => h.allSVars ++ χ.allSVars 
  | @substitution _ _ φ ψ X sfi h => X :: h.allSVars ++ ψ.allSVars 
  | @prefixpoint _ _ φ X sfi pos => X :: φ.allSVars
  | @knasterTarski _ _ φ ψ X sfi h => X :: h.allSVars
  | @Proof.singleton _ _ C₁ C₂ x φ => φ.allSVars ++ (C₁[⊥].allSVars) ++ (C₂[⊥].allSVars)






@[for_matching_logic]
def Proof.premisesUsed {Γ : Premises 𝕊} {φ : Pattern 𝕊} (proof : Proof Γ φ) : List <| Pattern 𝕊 := 
  match proof with 
  | @tautology _ _ φ _ => []
  | @premise _ _ φ _ hmem => [φ]
  | @modusPonens _ _ φ ψ h₁ h₂ =>  h₁.premisesUsed ++ h₂.premisesUsed 
  | @existQuan _ _ φ x y sfi => []
  | @existGen _ _ φ ψ x nfv h => h.premisesUsed 
  | @existence _ _ x => []
  | @propagationBottomLeft _ _ c => []
  | @propagationBottomRight _ _ c => []
  | @propagationDisjLeft _ _ φ ψ c => []
  | @propagationDisjRight _ _ φ ψ c => []
  | @propagationExistLeft _ _ φ x c nfv => []
  | @propagationExistRight _ _ φ x c nfv => []
  | @framingLeft _ _ φ ψ χ h => h.premisesUsed 
  | @framingRight _ _ φ ψ χ h => h.premisesUsed
  | @substitution _ _ φ ψ X sfi h => h.premisesUsed 
  | @prefixpoint _ _ φ X sfi pos => []
  | @knasterTarski _ _ φ ψ X sfi h => h.premisesUsed 
  | @Proof.singleton _ _ C₁ C₂ x φ => [] 


@[for_matching_logic]
def Proof.tautologiesUsed {Γ : Premises 𝕊} {φ : Pattern 𝕊} (proof : Proof Γ φ) : List <| Pattern 𝕊 := 
  match proof with 
  | @tautology _ _ φ _ => [φ]
  | @premise _ _ φ _ hmem => []
  | @modusPonens _ _ φ ψ h₁ h₂ =>  h₁.tautologiesUsed ++ h₂.tautologiesUsed 
  | @existQuan _ _ φ x y sfi => []
  | @existGen _ _ φ ψ x nfv h => h.tautologiesUsed 
  | @existence _ _ x => []
  | @propagationBottomLeft _ _ c => []
  | @propagationBottomRight _ _ c => []
  | @propagationDisjLeft _ _ φ ψ c => []
  | @propagationDisjRight _ _ φ ψ c => []
  | @propagationExistLeft _ _ φ x c nfv => []
  | @propagationExistRight _ _ φ x c nfv => []
  | @framingLeft _ _ φ ψ χ h => h.tautologiesUsed 
  | @framingRight _ _ φ ψ χ h => h.tautologiesUsed
  | @substitution _ _ φ ψ X sfi h => h.tautologiesUsed 
  | @prefixpoint _ _ φ X sfi pos => []
  | @knasterTarski _ _ φ ψ X sfi h => h.tautologiesUsed 
  | @Proof.singleton _ _ C₁ C₂ x φ => [] 


#check List.contains

-- 
def Proof.createEnv {Γ : Premises 𝕊} {φ : Pattern 𝕊} (proof : Proof Γ φ) 
  (shapes : List <| Shape 𝕊 := [])
  : Env := 
Id.run do 
  let mut env : Env := {}
  for symbol in proof.symbols do 
    env := env.addSymbol <| toMMClaim symbol 
  for evar in proof.allEVars do 
    env := env.addElementVar <| toMMClaim evar 
  for svar in proof.allSVars do 
    env := env.addSetVar <| toMMClaim svar 
  return env 