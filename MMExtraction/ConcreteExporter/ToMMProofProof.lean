import MatchingLogic 
import MMExtraction.MMBuilder
import MMExtraction.ConcreteExporter.ToMMClaim
import MMExtraction.ConcreteExporter.ToMMProof 
import MMExtraction.ConcreteExporter.Shape 
import MMExtraction.ConcreteExporter.Var
-- import MMExtraction.ConcreteExporter.Freshness 
-- import MMExtraction.ConcreteExporter.Positivity 
import MMExtraction.ConcreteExporter.ToLabel 
import MMExtraction.ConcreteExporter.MLITP

set_option autoImplicit false 
set_option linter.unusedVariables.patternVars false

namespace ML 
#check List.find?
open ML.Meta
open MLITP (Statement)



variable {ð : Type} [DecidableEq ð] [ToMMClaim ð] [Repr ð]

@[for_matching_logic, simp]
def Pattern.getFreshSVar : ML.Pattern ð â SVar 
  | Ï => .getFresh Ï.svars

def Proof.statements {Î : Premises ð} {Ï : Pattern ð} (proof : Proof Î Ï)
  (shapes : List <| Shape ð := [])
  : List <| Statement ð := 
  if shapes.find? (fun shape => shape Ï |>.isSome) |>.isSome
    then []
  else match proof with 
  | @tautology _ _ Ï _ => 
    [.tautology Ï]
  | @premise _ _ Ï _ hmem => 
    []
  | @modusPonens _ _ Ï Ï hâ hâ => 
    .union (hâ.statements shapes) (hâ.statements shapes)
  | @existQuan _ _ Ï x y sfi => 
    [.substitution (.evar x) (.evar y) Ï]
  | @existGen _ _ Ï Ï x nfv h => 
    h.statements shapes |>.insert <| .fresh (.evar x) Ï 
  | @existence _ _ x => 
    []
  | @propagationBottomLeft _ _ c => 
    []
  | @propagationBottomRight _ _ c => 
    []
  | @propagationDisjLeft _ _ Ï Ï c => 
    [] 
  | @propagationDisjRight _ _ Ï Ï c => 
    [] 
  | @propagationExistLeft _ _ Ï x c nfv => 
    []
  | @propagationExistRight _ _ Ï x c nfv => 
    []
  | @framingLeft _ _ Ï Ï Ï h => 
    [] 
  | @framingRight _ _ Ï Ï Ï h => 
    []
  | @substitution _ _ Ï Ï X sfi h => 
    h.statements shapes |>.insert <| .substitution (.svar X) Ï Ï
  | @prefixpoint _ _ Ï X pos sfi => 
    [.positive (.svar X) Ï]
  | @knasterTarski _ _ Ï Ï X sfi h => 
    h.statements shapes
  | @Proof.singleton _ _ Câ Câ x Ï => 
    []

protected def Proof.toMMProof {Î : Premises ð} {Ï : Pattern ð} (proof : Proof Î Ï)
  (shapes : List <| Shape ð := Shape.standardPropositional)
  (premiseShapes : List <| Shape ð := [])
  : Option MMProof := 
do 
  for matching in shapes do 
    if let some â¨parts, labelâ© := matching Ï then 
      return .app label <| parts.map fun â¨_, _, partâ© => toMMProof part 
  match proof with 
  | @tautology _ _ Ï _ => 
    return .app (Statement.tautology Ï |>.toLabel) []
  | @premise _ _ Ï _ hmem => 
    let mut result : Option MMProof := none 
    for matching in premiseShapes do 
      if let some â¨parts, labelâ© := matching Ï then 
        result := some <| .app label <| parts.map fun â¨_, _, partâ© => toMMProof part 
        break
    result
  | @modusPonens _ _ Ï Ï hâ hâ => 
    return .app "proof-rule-mp" [
      Ï.toMMProof,    -- ph0 
      Ï.toMMProof,    -- ph1 
      â hâ.toMMProof shapes premiseShapes, -- proof-rule-mp.1
      â hâ.toMMProof shapes premiseShapes -- proof-rule-mp.0
    ] 
  | @existQuan _ _ Ï x y sfi => 
    return .app "proof-rule-exists" [
      Ï[x âáµ y].toMMProof,                                             -- ph0
      Ï.toMMProof,                                                      -- ph1 
      x.toMMProof,                                                      -- x
      y.toMMProof,                                                      -- y 
      .app (Statement.substitution (.evar x) (.evar y) Ï |>.toLabel) [] -- proof-rule-exists.0
    ]
  | @existGen _ _ Ï Ï x nfv h => 
    return .app "proof-rule-gen" [
      Ï.toMMProof,                                      -- ph0
      Ï.toMMProof,                                      -- ph1
      x.toMMProof,                                      -- x
      â h.toMMProof shapes premiseShapes,                                    -- proof-rule-gen.0
      .app (Statement.fresh (.evar x) Ï |>.toLabel) []  -- proof-rule.gen.1 
    ]
  | @existence _ _ x => 
    return .app "proof-rule-existence" [
      x.toMMProof -- x 
    ]    
  | @propagationBottomLeft _ _ c => 
    return .app "proof-rule-propagation-bot" [
    -- add fresh #Pattern c and fresh #Variable xX together with the essential that ph' is a context in xX and that c the pattern is the substitution of bot in the context
  ]
  | @propagationBottomRight _ _ c => 
    let X : SVar := c.getFreshSVar 
    return .app "proof-rule-propagation-bot" [
      toMMProof <| X â¬ c,                                                       -- ph0
      toMMProof <| â¥ â¬ c,                                                       -- ph1
      toMMProof <| Var.svar X,                                                  -- xX
      .app (Statement.context (.svar X) (X â¬ c) |>.toLabel) [],                 -- proof-rule-propagation-bot.0
      .app (Statement.substitution (.svar X) â¥ (X â¬ c) (â¥ â¬ c) |>.toLabel) []   -- proof-rule-propagation-bot.1
    ]
  | @propagationDisjLeft _ _ Ï Ï c => 
    return .app "not-implemented" [] 
  | @propagationDisjRight _ _ Ï Ï c => 
    let X : SVar := Ï â¬ Ï â¬ c |>.getFreshSVar 
    return .app "proof-rule-propagation-or" [
      toMMProof <| X â¬ c,                                                       -- ph0
      toMMProof <| (Ï â Ï) â¬ c,                                                 -- ph1
      toMMProof <| Ï â¬ c,                                                       -- ph2
      toMMProof <| Ï â¬ c,                                                       -- ph3     
      toMMProof <| Var.svar X,                                                  -- xX
      .app (Statement.context (.svar X) (X â¬ c) |>.toLabel) [],                 -- proof-rule-propagation-or.0
      .app (Statement.substitution (.svar X) (Ï â Ï) (X â¬ c) |>.toLabel) [],    -- proof-rule-propagation-or.1 
      .app (Statement.substitution (.svar X) Ï (X â¬ c) |>.toLabel) [],          -- proof-rule-propagation-or.2
      .app (Statement.substitution (.svar X) Ï (X â¬ c) |>.toLabel) []           -- proof-rule-propagation-or.3
    ] 
  | @propagationExistLeft _ _ Ï x c nfv => 
    return .app "not-implemented" []
  | @propagationExistRight _ _ Ï x c nfv => 
    return .app "not-implemented" []
  | @framingLeft _ _ Ï Ï Ï h => 
    return .app "not-implemented" [] 
  | @framingRight _ _ Ï Ï c h => 
    let X := Ï â¬ Ï â¬ c |>.getFreshSVar 
    let C := c â¬ X 
    return .app "not-implemented" [
      toMMProof C,                                                     -- ph0
      toMMProof <| C[X âË¢ Ï],                                         -- ph1
      toMMProof <| C[X âË¢ Ï],                                         -- ph2
      toMMProof Ï,                                                     -- ph3 
      toMMProof Ï,                                                     -- ph4
      toMMProof <| Var.svar X,                                         -- xX 
      .app (Statement.context (.svar X) C |>.toLabel) [],              -- proof-rule-frame.0
      .app (Statement.substitution (.svar X) Ï C |>.toLabel) [],       -- proof-rule-frame.1
      .app (Statement.substitution (.svar X) Ï C |>.toLabel) [],       -- proof-rule-frame.2
      â h.toMMProof shapes premiseShapes                                                   -- proof-rule-frame.3
    ]
  | @substitution _ _ Ï Ï X sfi h => 
    return .app "proof-rule-set-var-substitution" [
      Ï[X âË¢ Ï].toMMProof,                                              -- ph0
      Ï.toMMProof,                                                       -- ph1
      Ï.toMMProof,                                                       -- ph2 
      X.toMMProof,                                                       -- X
      .app (MLITP.Statement.substitution (.svar X) Ï Ï |>.toLabel) [],   -- proof-rule-set-var-substitution.0
      â h.toMMProof shapes premiseShapes                                                     -- proof-rule-set-var-substitution.1
    ]
  | @prefixpoint _ _ Ï X pos sfi => 
    return .app "proof-rule-prefixpoint" [
      Ï.toMMProof,                                                      
      X.toMMProof /- here to insert `sfi`-/, 
      .app (MLITP.Statement.positive (.svar X) Ï |>.toLabel) []
    ]
  | @knasterTarski _ _ Ï Ï X sfi h => 
    return .app "proof-rule-kt" [
      Ï[X âË¢ Ï].toMMProof,
      Ï.toMMProof, 
      Ï.toMMProof, 
      X.toMMProof, 
      .app (Statement.substitution (.svar X) Ï Ï |>.toLabel) [],
      â h.toMMProof shapes premiseShapes
    ]
  | @Proof.singleton _ _ Câ Câ x Ï => 
    let X : SVar := /- placeholder -/ â¨101â©  
    let Y : SVar := /- placeholder -/ â¨102â© 
    return .app "proof-rule-singleton" [
      toMMProof <| Câ.insert X,                                                       -- ph0
      toMMProof <| Câ.insert X,                                                       -- ph1 
      toMMProof Ï,                                                                    -- ph2 
      toMMProof <| Câ.insert <| x â Ï,                                                -- ph3
      toMMProof <| Câ.insert <| x â â¼Ï,                                               -- ph4
      toMMProof x,                                                                    -- x
      toMMProof <| Var.svar X,                                                        -- xX
      toMMProof <| Var.svar Y,                                                        -- yY   
      .app (Statement.context (.svar X) (Câ.insert X) |>.toLabel) [],                 -- proof-rule-singleton.0
      .app (Statement.context (.svar Y) (Câ.insert Y) |>.toLabel) [],                 -- proof-rule-singleton.1
      .app (Statement.substitution (.svar X) (x â Ï) (Câ.insert X) |>.toLabel) [],    -- proof-rule-singleton.2
      .app (Statement.substitution (.svar Y) (x â â¼Ï) (Câ.insert Y) |>.toLabel) []    -- proof-rule-singleton.3
    ]

-- instance {Î : Premises ð} {Ï : Pattern ð} : ToMMProof <| Proof Î Ï := â¨Proof.toMMProofâ©






def thm (Ï Ï Ï : Pattern Empty) : â â¢ (Ï â Ï) â (Ï â Ï) â (Ï â Ï) := Proof.tautology <| by 
  unfold_tautology!
  intros h h' 
  exact h' â h

#eval thm â¥ â¤ â¥ |>.toMMProof 



#eval (@Proof.implSelf Empty â â¥).toMMProof (shapes := Shape.standardPropositional) |>.get!

#eval (@Proof.weakeningDisj Empty â â¤ â¥).toMMProof (shapes := Shape.standardPropositional) |>.get! 

#eval (@Proof.exFalso Empty â â¥).toMMProof |>.get!

-- â¥ â â¥       ?Ï â ?Ï 
-- â¤ â â¤       ?Ï â ?Ï

