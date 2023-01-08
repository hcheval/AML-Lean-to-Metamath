import MatchingLogic
import MMExtraction.Attributes

namespace ML 

deriving instance Repr for EVar 
deriving instance Repr for SVar 

def Var := EVar ⊕ SVar 
  deriving DecidableEq, Inhabited, Repr 

def Var.toPattern (𝕊 : Type) : Var → Pattern 𝕊 
| .inl x => .evar x 
| .inr X => .svar X 

@[rename_to "hasVar"]
def Pattern.isVar (φ : Pattern 𝕊) (xX : Var) : Bool := Sum.casesOn xX φ.isEvar φ.isSvar
  -- match xX with 
  -- | .inl x => φ.isEvar x 
  -- | .inr X => φ.isSvar X 

def lift (fEVar : EVar → α) (fSVar : SVar → α) : Var → α := 
  fun xX => match xX with 
  | .inl x => fEVar x 
  | .inr X => fSVar X

def Pattern.substVar (target : Pattern 𝕊) (var : Var) (substituent : Pattern 𝕊)  := 
  match var with 
  | .inl x => target[x ⇐ᵉ substituent]
  | .inr X => target[X ⇐ˢ substituent]

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
  | .evar x => [.inl x] 
  | .svar X => [.inr X]
  | φ ⇒ ψ | φ ⬝ ψ => φ.allVars ++ ψ.allVars 
  | ∃∃ x φ => .inl x :: φ.allVars 
  | μ X φ => .inr X :: φ.allVars 
  | _ => []

