import MatchingLogic
import MMExtraction.Attributes

namespace ML 

deriving instance Repr for EVar 
deriving instance Repr for SVar 

inductive Var where 
  | evar : EVar โ Var 
  | svar : SVar โ Var 
  deriving DecidableEq, Inhabited, Repr 

def Var.toPattern (๐ : Type) : Var โ Pattern ๐ 
| .evar x => .evar x 
| .svar X => .svar X 

@[rename_to "hasVar"]
def Pattern.isVar (ฯ : Pattern ๐) (xX : Var) : Bool := Var.casesOn xX ฯ.isEvar ฯ.isSvar
  -- match xX with 
  -- | .evar x => ฯ.isEvar x 
  -- | .svar X => ฯ.isSvar X 

def lift (fEVar : EVar โ ฮฑ) (fSVar : SVar โ ฮฑ) : Var โ ฮฑ := 
  fun xX => match xX with 
  | .evar x => fEVar x 
  | .svar X => fSVar X

def Pattern.substVar (target : Pattern ๐) (var : Var) (substituent : Pattern ๐)  := 
  match var with 
  | .evar x => target[x โแต substituent]
  | .svar X => target[X โหข substituent]

  notation ฯ "[" xX " โ " ฯ "]" => Pattern.substVar ฯ xX ฯ

def Pattern.allEVars : Pattern ๐ โ List EVar 
  | .evar x => [x] 
  | .svar X => []
  | ฯ โ ฯ | ฯ โฌ ฯ => ฯ.allEVars ++ ฯ.allEVars 
  | โโ x ฯ => x :: ฯ.allEVars 
  | ฮผ X ฯ => ฯ.allEVars 
  | _ => []

def Pattern.allSVars : Pattern ๐ โ List SVar 
  | .evar x => [] 
  | .svar X => [X]
  | ฯ โ ฯ | ฯ โฌ ฯ => ฯ.allSVars ++ ฯ.allSVars 
  | โโ x ฯ => ฯ.allSVars 
  | ฮผ X ฯ => X :: ฯ.allSVars 
  | _ => []

def Pattern.allVars : Pattern ๐ โ List Var 
  | .evar x => [.evar x] 
  | .svar X => [.svar X]
  | ฯ โ ฯ | ฯ โฌ ฯ => ฯ.allVars ++ ฯ.allVars 
  | โโ x ฯ => .evar x :: ฯ.allVars 
  | ฮผ X ฯ => .svar X :: ฯ.allVars 
  | _ => []

