import MatchingLogic 
import MMExtraction.MMBuilder
import MMExtraction.Tests

set_option autoImplicit false 

namespace ML 

open ML.Meta 

instance : ToString Empty where 
  toString := Empty.elim

class ToMMProof (α : Type)  where 
  toMMProof : α → MMProof

export ToMMProof (toMMProof)

def symbolToMMProof {𝕊 : Type} [ToString 𝕊] (σ : 𝕊) : MMProof := 
  .app s! "{σ}-is-symbol" []

/- The `ToString` instance should be replaced by some other identical class -/
instance {𝕊 : Type} [ToString 𝕊] : ToMMProof 𝕊 where 
  toMMProof := symbolToMMProof

/- Should be in the MatchingLogic project -/
instance : ToString EVar where 
  toString := toString ∘ EVar.val

def EVar.toMMClaim : EVar → String 
  | ⟨idx⟩ => s! "x{idx}"

protected def EVar.toMMProof : EVar → MMProof 
  | x => .app s! "{x.toMMClaim}-is-evar" []

/- Should be in the MatchingLogic project -/
instance : ToString SVar where 
  toString := toString ∘ SVar.val

def SVar.toMMClaim : SVar → String 
  | ⟨idx⟩ => s! "X{idx}"

protected def SVar.toMMProof : SVar → MMProof 
  | X => .app s! "{X.toMMClaim}-is-svar" []

instance : ToMMProof EVar where toMMProof := EVar.toMMProof
instance : ToMMProof SVar where toMMProof := SVar.toMMProof





variable {𝕊 : Type} [ToString 𝕊]

protected def Pattern.toMMProof : Pattern 𝕊 → MMProof 
| evar x => .app "var-is-pattern" [.app "element-var-is-var" [x.toMMProof]]
| svar X => .app "var-is-pattern" [.app "set-var-is-var" [X.toMMProof]]
| ⊥ => .app "bot-is-patter⬝" []
| φ ⇒ ψ => .app "imp-is-pattern" [φ.toMMProof, ψ.toMMProof]
| φ ⬝ ψ => .app "app-is-pattern" [φ.toMMProof, ψ.toMMProof]
| ∃∃ x φ => .app "exists-is-pattern" [x.toMMProof, φ.toMMProof] 
| μ X φ => .app "mu-is-pattern" [X.toMMProof, φ.toMMProof]
| symbol σ => .app "symbol-is-pattern" [symbolToMMProof σ]

instance : ToMMProof (Pattern 𝕊) where toMMProof := Pattern.toMMProof

def Pattern.toMMClaim : Pattern 𝕊 → String 
| evar x => x.toMMClaim
| svar X => X.toMMClaim
| ⊥ => "bot"
| φ ⇒ ψ => s! "( imp {φ.toMMClaim} {ψ.toMMClaim} )"
| φ ⬝ ψ => s! "( app {φ.toMMClaim} {ψ.toMMClaim} )"
| ∃∃ x φ => s! "( exists {x.toMMClaim} {φ.toMMClaim} )"
| μ X φ => s! "( mu {X.toMMClaim} {φ.toMMClaim} )"
| symbol σ => toString σ

def AppContext.toMMProof (var : String) : AppContext 𝕊 → MMProof  
| empty => .app "application-context-var" [.app s!"{var}-is-var" []]
| left φ C => .app "application-context-left" []
| right φ C => .app "application-context-right" []

def Proof.toMMProof {Γ : Premises 𝕊} {φ : Pattern 𝕊} : Proof Γ φ → MMProof 
| @tautology _ _ φ _ => .app "???tautology???" [φ.toMMProof]
| @premise _ _ φ _ hmem => .app "???premise???" [φ.toMMProof]
| @modusPonens _ _ φ ψ h₁ h₂ => .app "proof-rule-mp" [φ.toMMProof, ψ.toMMProof, h₁.toMMProof, h₂.toMMProof] 
| @existQuan _ _ φ x y sfi => .app "proof-rule-exists" [φ[x ⇐ᵉ y].toMMProof, φ.toMMProof, x.toMMProof, y.toMMProof /- here a proof of substitution -/]
| @existGen _ _ φ ψ x nfv h => .app "proof-rule-gen" [φ.toMMProof, ψ.toMMProof, h.toMMProof]
| @existence _ _ x => .app "proof-rule-existence" [x.toMMProof]
| @propagationBottomLeft _ _ c => .app "proof-rule-propagation-bot" [
  -- add fresh #Pattern c and fresh #Variable xX together with the essential that ph' is a context in xX and that c the pattern is the substitution of bot in the context
]
| @propagationBottomRight _ _ c => .app "not-implemented" []
| @propagationDisjLeft _ _ φ ψ c => .app "not-implemented" [] 
| @propagationDisjRight _ _ φ ψ c => .app "not-implemented" [] 
| @propagationExistLeft _ _ φ x c nfv => .app "not-implemented" []
| @propagationExistRight _ _ φ x c nfv => .app "not-implemented" []
| @framingLeft _ _ φ ψ χ h => .app "not-implemented" [] 
| @framingRight _ _ φ ψ χ h => .app "not-implemented" []
| @substitution _ _ φ ψ X sfi h => .app "proof-rule-set-var-substitution" [φ.toMMProof, ψ.toMMProof, X.toMMProof /- here to insert `sfi`-/ , h.toMMProof]
| @prefixpoint _ _ φ X sfi pos => .app "proof-rule-prefixpoint" [φ.toMMProof, X.toMMProof /- here to insert `sfi`-/ /- here to insert `pos`-/]
| @knasterTarski _ _ φ ψ X sfi h => .app "proof-rule-kt" [φ.toMMProof, ψ.toMMProof, X.toMMProof /- here to insert `sfi`-/, h.toMMProof]
| @Proof.singleton _ _ C₁ C₂ x φ => .app "proof-rule-singleton" [/- here to insert C₁ C₂ as proofs-/ x.toMMProof, φ.toMMProof]

example : @Pattern.toMMClaim Empty _ ⊥ = "bot" := by rfl 
example : @Pattern.toMMClaim Empty _ (.evar ⟨4⟩) = "x4" := by rfl 
example : @Pattern.toMMClaim Empty _ (.svar ⟨4⟩) = "X4" := by rfl 
example (n : ℕ) : @Pattern.toMMClaim Empty _ (.evar ⟨n⟩) = s!"x{n}" := by rfl 
example (n : ℕ) : @Pattern.toMMClaim Empty _ (.svar ⟨n⟩) = s!"X{n}" := by rfl 
example : @Pattern.toMMClaim Empty _ (⊥ ⇒ ⊥) = "( imp bot bot )" := by rfl  
example : @Pattern.toMMClaim Empty _ (⊥ ⇒ ⊥ ⇒ ⊥) = "( imp bot ( imp bot bot ) )" := by rfl
example : @Pattern.toMMClaim Empty _ ((⊥ ⇒ ⊥) ⇒ ⊥) = "( imp ( imp bot bot ) bot )" := by rfl
example : @Pattern.toMMClaim Empty _ (⊥ ⬝ ⊥) = "( app bot bot )" := by rfl 


-- TODO: move to MatchingLogic 
def Pattern.symbols : Pattern 𝕊 → Array 𝕊 
| symbol σ => #[σ]
| φ ⇒ ψ | φ ⬝ ψ => φ.symbols ++ ψ.symbols 
| ∃∃ _ φ | μ _ φ => φ.symbols 
| evar _ | svar _ | ⊥ => #[]

def Pattern.createEnv : Pattern 𝕊 → Env := fun φ ↦ Id.run do 
  let mut newenv : Env := {}
  for symbol in φ.symbols do 
    newenv := newenv.addSymbol <| toString symbol 
  for evar in φ.evars do 
    newenv := newenv.addElementVar evar.toMMClaim
  for svar in φ.svars do 
    newenv := newenv.addSetVar svar.toMMClaim 
  return newenv 


def n := 1000
def φ₀ : Pattern Empty := List.range n |>.map (Pattern.evar ∘ EVar.mk) |>.foldr Pattern.implication (init := Pattern.evar ⟨0⟩)

abbrev 𝕊₀ := Empty 

open Pattern Proof in 
def testTheorems : Array <| Σ (φ : Pattern 𝕊₀), Proof ∅ φ := #[
  ⟨∃∃ ⟨0⟩ (evar ⟨0⟩), existence⟩,
  ⟨∃∃ ⟨1⟩ (evar ⟨1⟩), existence⟩
]

deriving instance Repr for Empty 
deriving instance Repr for EVar 
deriving instance Repr for SVar 
deriving instance Repr for Pattern 

def reprln {α : Type _} [Repr α] (a : α) := IO.println <| repr a
/-
  C[φ] -----> χ₁ ((χ₂ φ) χ₃)
  χ₁ ((χ₂ X) χ₃) [φ] = 
-/


#eval show IO Unit from do 
  for ⟨testClaim, testProof⟩ in testTheorems do 
    reprln testClaim.toMMClaim
    reprln testProof.toMMProof
    IO.println ""




def Var := EVar ⊕ SVar 
  deriving DecidableEq, Inhabited, Repr 

def Var.toPattern : Var → Pattern 𝕊 
| .inl x => .evar x 
| .inr X => .svar X 

protected def Var.toMMProof : Var → MMProof 
  | .inl x => toMMProof x 
  | .inr X => toMMProof X

instance : ToMMProof Var where toMMProof := Var.toMMProof


inductive Fresh (xX : Var) : Pattern 𝕊 → Type where 
| var (yY : Var) : xX ≠ yY → Fresh xX yY.toPattern 
| symbol (σ : 𝕊) : Fresh xX (.symbol σ)
| bot : Fresh xX (⊥ : Pattern 𝕊)
| imp (φ ψ : Pattern 𝕊) : Fresh xX φ → Fresh xX ψ → Fresh xX (φ ⇒ ψ)
| app (φ ψ : Pattern 𝕊) : Fresh xX φ → Fresh xX ψ → Fresh xX (φ ⬝ ψ)
| exist (x : EVar) (φ : Pattern 𝕊) : xX ≠ .inl x → Fresh xX φ → Fresh xX (∃∃ x φ)
| existShadowed (x : EVar) (φ : Pattern 𝕊) : xX = .inl x → Fresh xX (∃∃ x φ)
| mu (X : SVar) (φ : Pattern 𝕊) : xX ≠ .inr X → Fresh xX φ → Fresh xX (μ X φ)
| muShadowed (X : SVar) (φ : Pattern 𝕊) : xX = .inr X → Fresh xX (μ X φ)

def autoFresh (xX : Var) (φ : Pattern 𝕊) : Option (Fresh xX φ) := do 
  match φ with 
  | .evar x =>
    if h : xX ≠ .inl x then return .var (.inl x) h
    else none 
  | .svar X =>  
    if h : xX ≠ .inr X then return .var (.inr X) h
    else none 
  | .symbol σ => return .symbol σ
  | ⊥ => return .bot 
  | φ₁ ⇒ φ₂ => return .imp φ₁ φ₂ (← autoFresh xX φ₁) (← autoFresh xX φ₂)
  | φ₁ ⬝ φ₂ => return .app φ₁ φ₂ (← autoFresh xX φ₁) (← autoFresh xX φ₂)
  | ∃∃ x ψ => 
    if h : xX ≠ .inl x then 
      return .exist x ψ h (← autoFresh xX ψ)
    else 
      return .existShadowed x ψ (by simp_all)
  | μ X ψ => 
    if h : xX ≠ .inr X then 
      return .mu X ψ h (← autoFresh xX ψ) 
    else 
      return .muShadowed X ψ (by simp_all)

def autoFreshEVar (x : EVar) (φ : Pattern 𝕊) : Option (Fresh (.inl x) φ) := 
  autoFresh (.inl x) φ

def autoFreshSVar (X : SVar) (φ : Pattern 𝕊) : Option (Fresh (.inr X) φ) := 
  autoFresh (.inr X) φ
  

def autoFreshDirect (xX : Var) (φ : Pattern 𝕊) : Option MMProof := do
  match φ with 
  | .evar x => 
    if xX != .inl x then 
      return .app "fresh-in-var" [toMMProof xX, toMMProof x] 
    else 
      none 
  | .svar X => 
    if xX != .inr X then 
      return .app "fresh-in-var" [toMMProof xX, toMMProof X]
    else 
      none 
  | .symbol σ => return .app "fresh-in-symbol" [toMMProof xX, toMMProof σ]
  | ⊥ => return .app "fresh-in-bot" [toMMProof xX]
  | φ₁ ⇒ φ₂ => return .app "fresh-in-imp" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, ← autoFreshDirect xX φ₁, ← autoFreshDirect xX φ₂]
  | φ₁ ⬝ φ₂ => return .app "fresh-in-app" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, ← autoFreshDirect xX φ₁, ← autoFreshDirect xX φ₂]
  | ∃∃ x ψ => 
    if xX != .inl x then 
      return .app "fresh-in-exists" [toMMProof xX, toMMProof ψ, ← autoFreshDirect xX ψ]
    else 
      return .app "fresh-in-exists-shadowed" [toMMProof xX, toMMProof ψ]
  | μ X ψ => 
    if xX != .inr X then 
      return .app "fresh-in-mu" [toMMProof xX, toMMProof ψ, ← autoFreshDirect xX ψ]
    else 
      return .app "fresh-in-mu-shadowed" [toMMProof xX, toMMProof ψ]


def autoFreshDirectEVar : EVar → Pattern 𝕊 → Option MMProof := autoFreshDirect ∘ .inl 

def autoFreshDirectSVar : SVar → Pattern 𝕊 → Option MMProof := autoFreshDirect ∘ .inr


-- should rename this with `has` 
def Pattern.isVar (φ : Pattern 𝕊) (xX : Var) : Bool := 
  match xX with 
  | .inl x => φ.isEvar x 
  | .inr X => φ.isSvar X 

mutual /- `autoPositive` `autoNegative`-/
  -- these are not partial, but I don't care about their termination for the time being 
  partial def autoPositive (xX : Var) (φ : Pattern 𝕊) : Option MMProof := do 
    if φ.isVar xX then 
      return .app "positive-disjoint" [toMMProof xX, toMMProof φ]
    else match φ with 
    | .evar x => return .app "positive-in-var" [toMMProof xX, toMMProof x] 
    | .svar X => return .app "positive-in-var" [toMMProof xX, toMMProof X]
    | .symbol σ => return .app "positive-in-symbol" [toMMProof xX, toMMProof σ]
    | ⊥ => return .app "positive-in-bot" [toMMProof xX]
    | φ₁ ⇒ φ₂ => return .app "positive-in-imp" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, ← autoNegative xX φ₁, ← autoPositive xX φ₂]
    | φ₁ ⬝ φ₂ => return .app "positive-in-app" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, ← autoPositive xX φ₁, ← autoPositive xX φ₂] 
    | ∃∃ x ψ => return .app "positive-in-exists" [toMMProof xX, toMMProof ψ, ← autoPositive xX ψ]
    | μ X ψ => return .app "positive-in-mu" [toMMProof xX, toMMProof ψ, ← autoPositive xX ψ]

  partial def autoNegative (xX : Var) (φ : Pattern 𝕊) : Option MMProof := do 
    if φ.isVar xX then 
      return .app "negative-disjoint" [toMMProof xX, toMMProof φ]
    else match φ with 
    | .evar x => 
      if xX != .inl x then 
        return .app "negative-in-var" [toMMProof xX, toMMProof x] 
      else none -- this I think is needed to match the MM definition, but evars should never be negative, the notion does not exist for them
    | .svar X => 
      if xX != .inr X then 
        return .app "negative-in-var" [toMMProof xX, toMMProof X]
      else none 
    | .symbol σ => return .app "negative-in-symbol" [toMMProof xX, toMMProof σ]
    | ⊥ => return .app "negative-in-bot" [toMMProof xX]
    | φ₁ ⇒ φ₂ => return .app "negative-in-imp" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, ← autoPositive xX φ₁, ← autoNegative xX φ₂]
    | φ₁ ⬝ φ₂ => return .app "negative-in-app" [toMMProof xX, toMMProof φ₁, toMMProof φ₂, ← autoNegative xX φ₁, ← autoNegative xX φ₂] 
    | ∃∃ x ψ => return .app "negative-in-exists" [toMMProof xX, toMMProof ψ, ← autoNegative xX ψ]
    | μ X ψ => return .app "negative-in-mu" [toMMProof xX, toMMProof ψ, ← autoNegative xX ψ]
end 

#eval autoPositive (.inr ⟨0⟩) (.svar ⟨0⟩ ⇒ ⊥ : Pattern Bool) 

variable [DecidableEq 𝕊] 

deriving instance DecidableEq for Pattern 

-- def autoSubstitution (target substituent : Pattern 𝕊) (xX : Var) : Option MMProof := do 
--   match target with 
--   | .evar x => 
--     if .inl x == xX then 
--       return .app "substitution-var-same" [toMMProof xX, toMMProof substituent]
--     else 
--       return .app "substitution-var-diff" [toMMProof x, toMMProof substituent, toMMProof xX]
--   | .symbol σ => 
--     return .app "substitution-symbol" [toMMProof σ, toMMProof substituent, toMMProof xX]
--   | ⊥ => 
--     return .app "substitution-bot" [toMMProof (⊥ : Pattern 𝕊), toMMProof substituent, toMMProof xX]
--   | _ => none -- should not happen



inductive Substitution : Pattern 𝕊 → Pattern 𝕊 → Pattern 𝕊 → Var → Type where 
| varSame (xX yY : Var) (φ : Pattern 𝕊) (ψ : Pattern 𝕊) : 
  xX = yY → φ = ψ → Substitution φ yY.toPattern ψ xX
| varDiff (xX : Var) (φ : Pattern 𝕊) (yY : Var) :
  xX = yY → Substitution yY.toPattern yY.toPattern φ xX
| symbol (xX : Var) (φ : Pattern 𝕊) (σ : 𝕊) : 
  Substitution (.symbol σ) (.symbol σ) φ xX 
| bot (xX : Var) (φ : Pattern 𝕊) : 
  Substitution ⊥ ⊥ φ xX 
| imp (xX : Var) (φ : Pattern 𝕊) (ψ₁ ψ₂ s₁ s₂ : Pattern 𝕊) : 
  Substitution s₁ ψ₁ φ xX → Substitution s₂ ψ₂ φ xX → Substitution (s₁ ⇒ s₂) (ψ₁ ⇒ ψ₂) φ xX 
| app (xX : Var) (φ : Pattern 𝕊) (ψ₁ ψ₂ s₁ s₂ : Pattern 𝕊) : 
  Substitution s₁ ψ₁ φ xX → Substitution s₂ ψ₂ φ xX → Substitution (s₁ ⬝ s₂) (ψ₁ ⬝ ψ₂) φ xX 



-- this is probably way to well-specified in the type and probably a bad idea 
-- will lead to DTT hell.
def autoSubstitutionEVar (result target substituent : Pattern 𝕊) (x : EVar) : 
  result = target[x ⇐ᵉ substituent] → Option (Substitution result target substituent (.inl x)) := 
fun h => do 
  match target with 
  | .evar y => 
    if h' : x = y then 
      return .varSame (.inl x) (.inl y) _ _ (by rw [h']) (by simp_all)
    else 
      return .varDiff _ _ _ _
  | _ => none 

