import MatchingLogic
import MMExtraction.Attributes

namespace ML 

deriving instance Repr for EVar 
deriving instance Repr for SVar 

inductive Var where 
  | evar : EVar → Var 
  | svar : SVar → Var 
  deriving DecidableEq, Inhabited, Repr 

def Var.toPattern (𝕊 : Type) : Var → Pattern 𝕊 
| .evar x => .evar x 
| .svar X => .svar X 

@[rename_to "hasVar"]
def Pattern.isVar (φ : Pattern 𝕊) (xX : Var) : Bool := Var.casesOn xX φ.isEvar φ.isSvar
  -- match xX with 
  -- | .evar x => φ.isEvar x 
  -- | .svar X => φ.isSvar X 

def lift (fEVar : EVar → α) (fSVar : SVar → α) : Var → α := 
  fun xX => match xX with 
  | .evar x => fEVar x 
  | .svar X => fSVar X

def Pattern.substVar (target : Pattern 𝕊) (var : Var) (substituent : Pattern 𝕊)  := 
  match var with 
  | .evar x => target[x ⇐ᵉ substituent]
  | .svar X => target[X ⇐ˢ substituent]

  notation φ "[" xX " ⇐ " ψ "]" => Pattern.substVar φ xX ψ

def Pattern.allEVars : Pattern 𝕊 → List EVar 
  | .evar x => [x] 
  | .svar X => []
  | φ ⇒ ψ | φ ⬝ ψ => φ.allEVars ++ ψ.allEVars 
  | ∃∃ x φ => x :: φ.allEVars 
  | μ X φ => φ.allEVars 
  | _ => []

def Pattern.allSVars : Pattern 𝕊 → List SVar 
  | .evar x => [] 
  | .svar X => [X]
  | φ ⇒ ψ | φ ⬝ ψ => φ.allSVars ++ ψ.allSVars 
  | ∃∃ x φ => φ.allSVars 
  | μ X φ => X :: φ.allSVars 
  | _ => []

def Pattern.allVars : Pattern 𝕊 → List Var 
  | .evar x => [.evar x] 
  | .svar X => [.svar X]
  | φ ⇒ ψ | φ ⬝ ψ => φ.allVars ++ ψ.allVars 
  | ∃∃ x φ => .evar x :: φ.allVars 
  | μ X φ => .svar X :: φ.allVars 
  | _ => []

