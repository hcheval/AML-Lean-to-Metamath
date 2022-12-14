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

variable {ð : Type} [ToMMClaim ð] 

@[for_matching_logic]
def Pattern.symbols : Pattern ð â List ð 
| symbol Ï => [Ï]
| Ï â Ï | Ï â¬ Ï => Ï.symbols ++ Ï.symbols 
| ââ _ Ï | Î¼ _ Ï => Ï.symbols 
| evar _ | svar _ | â¥ => []

@[for_matching_logic]
def AppContext.patterns := @AppContext.toList 

def Pattern.createEnv : Pattern ð â Env := fun Ï â¦ Id.run do 
  let mut newenv : Env := {}
  for symbol in Ï.symbols do 
    newenv := newenv.addSymbol <| toMMClaim symbol 
  for evar in Ï.evars do 
    newenv := newenv.addElementVar evar.toMMClaim
  for svar in Ï.svars do 
    newenv := newenv.addSetVar svar.toMMClaim 
  return newenv 


def Proof.symbols {Î : Premises ð} {Ï : Pattern ð} (proof : Proof Î Ï) : List ð :=
  match proof with 
  | @tautology _ _ Ï _ => Ï.symbols
  | @premise _ _ Ï _ hmem => Ï.symbols
  | @modusPonens _ _ Ï Ï hâ hâ => hâ.symbols ++ hâ.symbols 
  | @existQuan _ _ Ï x y sfi => Ï.symbols
  | @existGen _ _ Ï Ï x nfv h => h.symbols
  | @existence _ _ x => []
  | @propagationBottomLeft _ _ c => c.symbols
  | @propagationBottomRight _ _ c => c.symbols
  | @propagationDisjLeft _ _ Ï Ï c => Ï.symbols ++ Ï.symbols ++ c.symbols
  | @propagationDisjRight _ _ Ï Ï c => Ï.symbols ++ Ï.symbols ++ c.symbols 
  | @propagationExistLeft _ _ Ï x c nfv => Ï.symbols ++ c.symbols
  | @propagationExistRight _ _ Ï x c nfv => Ï.symbols ++ c.symbols 
  | @framingLeft _ _ Ï Ï Ï h => h.symbols ++ Ï.symbols 
  | @framingRight _ _ Ï Ï Ï h => h.symbols ++ Ï.symbols 
  | @substitution _ _ Ï Ï X sfi h => h.symbols ++ Ï.symbols 
  | @prefixpoint _ _ Ï X sfi pos => Ï.symbols
  | @knasterTarski _ _ Ï Ï X sfi h => h.symbols
  | @Proof.singleton _ _ Câ Câ x Ï => Ï.symbols ++ (Câ[â¥].symbols) ++ (Câ[â¥].symbols)

def Proof.allEVars {Î : Premises ð} {Ï : Pattern ð} (proof : Proof Î Ï) : List EVar :=
  match proof with 
  | @tautology _ _ Ï _ => Ï.allEVars
  | @premise _ _ Ï _ hmem => Ï.allEVars
  | @modusPonens _ _ Ï Ï hâ hâ => hâ.allEVars ++ hâ.allEVars 
  | @existQuan _ _ Ï x y sfi => x :: y :: Ï.allEVars
  | @existGen _ _ Ï Ï x nfv h => x :: h.allEVars
  | @existence _ _ x => [x]
  | @propagationBottomLeft _ _ c => c.allEVars
  | @propagationBottomRight _ _ c => c.allEVars
  | @propagationDisjLeft _ _ Ï Ï c => Ï.allEVars ++ Ï.allEVars ++ c.allEVars
  | @propagationDisjRight _ _ Ï Ï c => Ï.allEVars ++ Ï.allEVars ++ c.allEVars 
  | @propagationExistLeft _ _ Ï x c nfv => x :: Ï.allEVars ++ c.allEVars
  | @propagationExistRight _ _ Ï x c nfv => x :: Ï.allEVars ++ c.allEVars 
  | @framingLeft _ _ Ï Ï Ï h => h.allEVars ++ Ï.allEVars 
  | @framingRight _ _ Ï Ï Ï h => h.allEVars ++ Ï.allEVars 
  | @substitution _ _ Ï Ï X sfi h => h.allEVars ++ Ï.allEVars 
  | @prefixpoint _ _ Ï X sfi pos => Ï.allEVars
  | @knasterTarski _ _ Ï Ï X sfi h => h.allEVars
  | @Proof.singleton _ _ Câ Câ x Ï => Ï.allEVars ++ (Câ[â¥].allEVars) ++ (Câ[â¥].allEVars)

def Proof.allSVars {Î : Premises ð} {Ï : Pattern ð} (proof : Proof Î Ï) : List SVar :=
  match proof with 
  | @tautology _ _ Ï _ => Ï.allSVars
  | @premise _ _ Ï _ hmem => Ï.allSVars
  | @modusPonens _ _ Ï Ï hâ hâ => hâ.allSVars ++ hâ.allSVars 
  | @existQuan _ _ Ï x y sfi => Ï.allSVars
  | @existGen _ _ Ï Ï x nfv h => h.allSVars
  | @existence _ _ x => []
  | @propagationBottomLeft _ _ c => c.allSVars
  | @propagationBottomRight _ _ c => c.allSVars
  | @propagationDisjLeft _ _ Ï Ï c => Ï.allSVars ++ Ï.allSVars ++ c.allSVars
  | @propagationDisjRight _ _ Ï Ï c => Ï.allSVars ++ Ï.allSVars ++ c.allSVars 
  | @propagationExistLeft _ _ Ï x c nfv => Ï.allSVars ++ c.allSVars
  | @propagationExistRight _ _ Ï x c nfv => Ï.allSVars ++ c.allSVars 
  | @framingLeft _ _ Ï Ï Ï h => h.allSVars ++ Ï.allSVars 
  | @framingRight _ _ Ï Ï Ï h => h.allSVars ++ Ï.allSVars 
  | @substitution _ _ Ï Ï X sfi h => X :: h.allSVars ++ Ï.allSVars 
  | @prefixpoint _ _ Ï X sfi pos => X :: Ï.allSVars
  | @knasterTarski _ _ Ï Ï X sfi h => X :: h.allSVars
  | @Proof.singleton _ _ Câ Câ x Ï => Ï.allSVars ++ (Câ[â¥].allSVars) ++ (Câ[â¥].allSVars)






@[for_matching_logic]
def Proof.premisesUsed {Î : Premises ð} {Ï : Pattern ð} (proof : Proof Î Ï) : List <| Pattern ð := 
  match proof with 
  | @tautology _ _ Ï _ => []
  | @premise _ _ Ï _ hmem => [Ï]
  | @modusPonens _ _ Ï Ï hâ hâ =>  hâ.premisesUsed ++ hâ.premisesUsed 
  | @existQuan _ _ Ï x y sfi => []
  | @existGen _ _ Ï Ï x nfv h => h.premisesUsed 
  | @existence _ _ x => []
  | @propagationBottomLeft _ _ c => []
  | @propagationBottomRight _ _ c => []
  | @propagationDisjLeft _ _ Ï Ï c => []
  | @propagationDisjRight _ _ Ï Ï c => []
  | @propagationExistLeft _ _ Ï x c nfv => []
  | @propagationExistRight _ _ Ï x c nfv => []
  | @framingLeft _ _ Ï Ï Ï h => h.premisesUsed 
  | @framingRight _ _ Ï Ï Ï h => h.premisesUsed
  | @substitution _ _ Ï Ï X sfi h => h.premisesUsed 
  | @prefixpoint _ _ Ï X sfi pos => []
  | @knasterTarski _ _ Ï Ï X sfi h => h.premisesUsed 
  | @Proof.singleton _ _ Câ Câ x Ï => [] 


@[for_matching_logic]
def Proof.tautologiesUsed {Î : Premises ð} {Ï : Pattern ð} (proof : Proof Î Ï) : List <| Pattern ð := 
  match proof with 
  | @tautology _ _ Ï _ => [Ï]
  | @premise _ _ Ï _ hmem => []
  | @modusPonens _ _ Ï Ï hâ hâ =>  hâ.tautologiesUsed ++ hâ.tautologiesUsed 
  | @existQuan _ _ Ï x y sfi => []
  | @existGen _ _ Ï Ï x nfv h => h.tautologiesUsed 
  | @existence _ _ x => []
  | @propagationBottomLeft _ _ c => []
  | @propagationBottomRight _ _ c => []
  | @propagationDisjLeft _ _ Ï Ï c => []
  | @propagationDisjRight _ _ Ï Ï c => []
  | @propagationExistLeft _ _ Ï x c nfv => []
  | @propagationExistRight _ _ Ï x c nfv => []
  | @framingLeft _ _ Ï Ï Ï h => h.tautologiesUsed 
  | @framingRight _ _ Ï Ï Ï h => h.tautologiesUsed
  | @substitution _ _ Ï Ï X sfi h => h.tautologiesUsed 
  | @prefixpoint _ _ Ï X sfi pos => []
  | @knasterTarski _ _ Ï Ï X sfi h => h.tautologiesUsed 
  | @Proof.singleton _ _ Câ Câ x Ï => [] 


#check List.contains

-- 
def Proof.createEnv {Î : Premises ð} {Ï : Pattern ð} (proof : Proof Î Ï) 
  (premiseShapes : List <| Shape ð := [])
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