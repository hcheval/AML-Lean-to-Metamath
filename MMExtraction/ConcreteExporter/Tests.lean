import MMExtraction.ConcreteExporter

namespace ML 

def runTestArray [Repr α] [Repr β] [BEq β] (f : α → β) (tests : Array <| α × β) (logging : Bool := true) : IO <| Array α := do 
  let mut failed : Array α := #[]
  let log : String → IO Unit := if logging then IO.println else fun _ => pure ⟨⟩
  for ⟨test, expected⟩ in tests do 
    if f test != expected then 
      log <| s!"Failed test {repr test}. Expected {repr <| f test} = {repr expected}"
      failed := failed.push test
  if failed.size > 0 then 
    log <| s! "Failed {failed.size} tests."
  else 
    log "All tests passed."
  return failed 

-- Tests for pattern to claim 
section PatternToClaim variable {𝕊 : Type} [Repr 𝕊] [ToMMClaim 𝕊]

  def tests₁ : Array <| Pattern Empty × String := #[
      ⟨⊥, "\\bot"⟩,
      ⟨.evar ⟨4⟩, "x4"⟩,
      ⟨.svar ⟨4⟩, "X4"⟩,  
      ⟨⊥ ⇒ ⊥, "( \\imp \\bot \\bot )"⟩,
      ⟨⊥ ⇒ ⊥ ⇒ ⊥, "( \\imp \\bot ( \\imp \\bot \\bot ) )"⟩,
      ⟨(⊥ ⇒ ⊥) ⇒ ⊥, "( \\imp ( \\imp \\bot \\bot ) \\bot )"⟩,
      ⟨⊥ ⬝ ⊥, "( \\app \\bot \\bot )"⟩,
      ⟨⊥ ⬝ ⊥ ⬝ ⊥,"( \\app ( \\app \\bot \\bot ) \\bot )"⟩,
      ⟨⊥ ⬝ (⊥ ⬝ ⊥), "( \\app \\bot ( \\app \\bot \\bot ) )"⟩,
      ⟨∃∃ ⟨3⟩ (.evar ⟨3⟩), "( \\exists x3 x3 )"⟩,
      ⟨μ ⟨3⟩ (.svar ⟨3⟩), "( \\mu X3 X3 )"⟩
    ]

  inductive Signature where 
  | a | b | c 
    deriving Repr 

  instance : ToMMClaim Signature where 
    toMMClaim := fun σ => 
      match σ with
        | .a => "a"
        | .b => "b"
        | .c => "c"
    
  def testsSignature : Array <| Pattern Signature × String := #[
    ⟨.symbol .a, "a"⟩,
    ⟨.symbol .b, "b"⟩,
    ⟨.symbol .c, "c"⟩
  ]

  instance : ToMMClaim Definedness where 
    toMMClaim := (fun .defined => "\\definedness")

  def testsDefinedness : Array <| Pattern Definedness × String := #[
    ⟨⌈⊥⌉, "( app \\definedness bot )"⟩
  ]


  #eval runTestArray Pattern.toMMClaim tests₁

  #eval runTestArray Pattern.toMMClaim testsSignature 

  deriving instance Repr for Definedness
  #eval runTestArray Pattern.toMMClaim testsDefinedness

end PatternToClaim






-- Tests for proof 
section WithVerifier variable {𝕊 : Type} [ToMMClaim 𝕊]

  def theorems : Array <| Σ φ : Pattern 𝕊, Proof ∅ φ := #[
    ⟨_, @ML.Proof.existence 𝕊 ∅ (⟨0⟩)⟩
  ]

end WithVerifier