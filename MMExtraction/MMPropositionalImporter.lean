import Lean 
import Mathlib 
import MatchingLogic

set_option autoImplicit false 

open Std (HashMap)

namespace ML.Meta 

def test : String := " ${
    rule-imp-transitivity.0 $e |- ( \\imp ph0 ph1 ) $.
    rule-imp-transitivity.1 $e |- ( \\imp ph1 ph2 ) $.
    rule-imp-transitivity $p |- ( \\imp ph0 ph2 ) $=
      ph0-is-pattern ph1-is-pattern imp-is-pattern ph0-is-pattern
      ph2-is-pattern imp-is-pattern ph0-is-pattern ph1-is-pattern
      ph2-is-pattern imp-is-pattern imp-is-pattern ph0-is-pattern
      ph1-is-pattern imp-is-pattern ph0-is-pattern ph2-is-pattern
      imp-is-pattern imp-is-pattern ph0-is-pattern ph1-is-pattern
      ph2-is-pattern proof-rule-prop-2 ph1-is-pattern ph2-is-pattern
      imp-is-pattern ph0-is-pattern ph1-is-pattern ph2-is-pattern
      imp-is-pattern imp-is-pattern ph1-is-pattern ph2-is-pattern
      imp-is-pattern ph0-is-pattern proof-rule-prop-1 rule-imp-transitivity.1
      proof-rule-mp proof-rule-mp rule-imp-transitivity.0 proof-rule-mp $.
$}"

def test' : String := " ${
    rule-imp-transitivity.0 $e |- ( \\imp ph0 ph1 ) $.
    rule-imp-transitivity.1 $e |- ( \\imp ph1 ph2 ) $.
    rule-imp-transitivity $p |- ( \\imp ph0 ph2 ) $=
      ph0-is-pattern ph1-is-pattern imp-is-pattern 
$}"

def testMultiple := " ${
    rule-imp-transitivity.0 $e |- ( \\imp ph0 ph1 ) $.
    rule-imp-transitivity.1 $e |- ( \\imp ph1 ph2 ) $.
    rule-imp-transitivity $p |- ( \\imp ph0 ph2 ) $=
      ph0-is-pattern ph1-is-pattern imp-is-pattern ph0-is-pattern
      ph2-is-pattern imp-is-pattern ph0-is-pattern ph1-is-pattern
      ph2-is-pattern imp-is-pattern imp-is-pattern ph0-is-pattern
      ph1-is-pattern imp-is-pattern ph0-is-pattern ph2-is-pattern
      imp-is-pattern imp-is-pattern ph0-is-pattern ph1-is-pattern
      ph2-is-pattern proof-rule-prop-2 ph1-is-pattern ph2-is-pattern
      imp-is-pattern ph0-is-pattern ph1-is-pattern ph2-is-pattern
      imp-is-pattern imp-is-pattern ph1-is-pattern ph2-is-pattern
      imp-is-pattern ph0-is-pattern proof-rule-prop-1 rule-imp-transitivity.1
      proof-rule-mp proof-rule-mp rule-imp-transitivity.0 proof-rule-mp $.
$}

${
    rule-imp-transitivity.0 $e |- ( \\imp ph0 ph1 ) $.
    rule-imp-transitivity.1 $e |- ( \\imp ph1 ph2 ) $.
    rule-imp-transitivity2 $p |- ( \\imp ph0 ph2 ) $=
      ph0-is-pattern ph1-is-pattern imp-is-pattern ph0-is-pattern
      ph2-is-pattern imp-is-pattern ph0-is-pattern ph1-is-pattern
      ph2-is-pattern imp-is-pattern imp-is-pattern ph0-is-pattern
      ph1-is-pattern imp-is-pattern ph0-is-pattern ph2-is-pattern
      imp-is-pattern imp-is-pattern ph0-is-pattern ph1-is-pattern
      ph2-is-pattern proof-rule-prop-2 ph1-is-pattern ph2-is-pattern
      imp-is-pattern ph0-is-pattern ph1-is-pattern ph2-is-pattern
      imp-is-pattern imp-is-pattern ph1-is-pattern ph2-is-pattern
      imp-is-pattern ph0-is-pattern proof-rule-prop-1 rule-imp-transitivity.1
      proof-rule-mp proof-rule-mp rule-imp-transitivity.0 proof-rule-mp $.
$}
"


def Var := String 

def Label := String 
  deriving Hashable, DecidableEq

def tokenize (source : String) : List String := source.split Char.isWhitespace |>.remove ""

structure PropositionalTheorem where 
  patterns : List Var 
  premises : HashMap Label String 
  claim : String 
  proof : List Label
  

inductive TokenKind where 
| const | var | floating | essential | provable | proof | symbol | beginScope | endScope
  deriving DecidableEq, Repr 


def getTokenKind (token : String) : TokenKind := 
  match token with 
  | "$c" => .const 
  | "$v" => .var 
  | "$f" => .floating 
  | "$e" => .essential 
  | "$p" => .provable 
  | "$=" => .proof 
  | "${" => .beginScope
  | "$}" => .endScope
  | _ => .symbol


def getPatternMVarNameFromLabelHeuristically (token : String) : Option String := 
  let suffix := "-is-pattern"
  if token.endsWith suffix then 
    some <| token.drop suffix.length 
  else 
    none 

def isPatternNameHeuristically (token : String) : Bool := 
  getPatternMVarNameFromLabelHeuristically token |>.isSome 


inductive ParsedProof where 
| app : String → List ParsedProof → ParsedProof 
  deriving Inhabited, Repr 

structure ParsedTheorem where 
  name : String := ""
  claim : Array String := #[] -- should replace with structure parsed representation of patterns 
  proof : ParsedProof := .app "" []
  essentials : List (Array String) := []
  patterns : Array String := #[]
  deriving Inhabited, Repr

def ParsedTheorem.reprCustom (parsedTheorem : ParsedTheorem) : Lean.Format := 
    repr { parsedTheorem with proof := .app "" [] }

def ParsedTheorem.arity (parsedTheorem : ParsedTheorem) : ℕ := 
  parsedTheorem.essentials.length + parsedTheorem.patterns.size


def getParsedTheoremWithName (name : String) (parsedTheorems : Array ParsedTheorem) : Option ParsedTheorem := Id.run do 
  parsedTheorems.toList.find? fun thm => thm.name == name 

def getArity? (label : String) (known : Array ParsedTheorem) : Option ℕ :=
  if let some thm := getParsedTheoremWithName label known then 
    return thm.arity
  else match label with 
  | "proof-rule-prop-1"         => some 2
  | "proof-rule-prop-2"         => some 3 
  | "proof-rule-prop-3"         => some 1
  | "proof-rule-mp"             => some 4 
  | "imp-is-pattern"            => some 2 
  | "rule-imp-transitivity.1"   => some 2 
  | "rule-imp-transitivity.0"   => some 2
  | _ => 
    if isPatternNameHeuristically label then some 0 else none 


def ParsedProof.isEmpty (parsedProof : ParsedProof) : Bool := 
  match parsedProof with 
  | app "" _ => true 
  | _ => false 

def parseProof (tokens : List String) (known : Array ParsedTheorem) : ParsedProof := Id.run do 
  let mut stack : List ParsedProof := []
  for token in tokens do 
    if let some arity := getArity? token known then 
      let args := stack.take arity 
      for _ in List.range arity do
        stack := stack.tail 
      stack := .app token args :: stack
    else  
      dbg_trace s! "Parse error: Unknown label {token}"
  return stack.head!

open String (Pos)

def isTokenEnd (c : Char) := c.isWhitespace

#check String.nextWhile
 
def nextToken (source : String) (start : Pos) : String × Pos := 
  let tokenStart := source.nextWhile Char.isWhitespace start
  let tokenEnd := source.nextWhile (fun c => !isTokenEnd c) tokenStart
  ⟨Substring.mk source tokenStart tokenEnd |>.toString, tokenEnd⟩

-- just for test of `nextToken`
def tokenize' (source : String) : Array (String × Pos) := Id.run do 
  let mut current : Pos := 0 
  let mut result : Array (String × Pos) := #[]
  while current < source.endPos do 
    let mut token := ""
    ⟨token, current⟩ := nextToken source current 
    result := result.push ⟨token, current⟩
  return result 


def forwardUntil (source : String) (start : Pos) (endToken : String) : Pos := Id.run do 
  let mut current := start 
  let mut token := ""
  while token != endToken && current ≤ source.endPos do 
    ⟨token, current⟩ := nextToken source current 
  return current 



def isPatternEndingToken (token : String) : Bool := 
  token == "$." || token == "$="

def nextPattern (source : String) (start : Pos) : (Array String) × Pos := Id.run do 
  let mut current := start 
  let mut token := ""
  let mut tokens : Array String := #[]
  while !isPatternEndingToken token && current ≤ source.endPos do 
    ⟨token, current⟩ := nextToken source current 
    tokens := tokens.push token
  return ⟨tokens, current⟩

def nextProof (source : String) (start : Pos) : (Array String) × Pos := Id.run do 
  let mut current := start 
  let mut token := ""
  let mut tokens : Array String := #[]
  while token != "$." && current < source.endPos do 
    ⟨token, current⟩ := nextToken source current 
    if token.trim.isEmpty then 
      continue 
    tokens := tokens.push token 
  return ⟨tokens, current⟩





/--
  Parses a mm statement of the form `<theorem claim> $= ... proof ...$.` where `<theorem claim>` should be a pattern,
  and returns it as a `ParsedProof` with no essentials.

  Advances the cursor.

  This function does *not* set the `name` of `ParsedProof`;
  it should instead be set by the caller with the token preceeding the theorem.
-/
def parseProvable (source : String) (start : Pos) (known : Array ParsedTheorem) : ParsedTheorem × Pos := Id.run do 
  let mut current := start 
  let mut pattern : Array String := #[]
  let mut proof : Array String := default 
  ⟨pattern, current⟩ := nextPattern source current 
  ⟨proof, current⟩ := nextProof source current 
  return ⟨⟨"", pattern, parseProof proof.toList.dropLast known, [], #[]⟩, current⟩

/--
  Parses a mm propositional theorem of the form 
  `${ <hyp₀> |- <patt₀> ... <hypₙ> |- <pattₙ> <thm name> $p = ... <proof> $. $}` 
  into a `ParsedProof` containing its essentials hypotheses (as patterns), name, claim (as patterns) 
  and parsed proof. 

  Advances the cursor.
-/
def parseScopedPropositionalTheorem (source : String) (start : Pos) (known : Array ParsedTheorem) : ParsedTheorem × Pos := Id.run do 

  let mut current : Pos := start
  let mut token : String := ""
  let mut token' : String := ""
  let mut parsedTheorem : ParsedTheorem := default 
  while token.trim != "$}" && current < source.endPos do 
    ⟨token, current⟩ := nextToken source current 
    if token.trim.isEmpty then 
      continue 
    match getTokenKind token with 
    | .symbol => 
      -- if token != "$}" then
      ⟨token', current⟩ := nextToken source current
      match getTokenKind token' with 
      | .essential => 
        let mut patt : Array String := #[]
        ⟨patt, current⟩ := nextPattern source current 
        parsedTheorem := { parsedTheorem with essentials := patt :: parsedTheorem.essentials}
      | .provable => 
        let mut proof : ParsedProof := default 
        let mut claim : Array String := default 
        ⟨⟨_, claim, proof, _, _⟩, current⟩ := parseProvable source current known
        parsedTheorem := { parsedTheorem with claim := claim, proof := proof, name := token }
      | _ => continue
    | .endScope => break
    | _ => continue
  if !parsedTheorem.proof.isEmpty then 
    return ⟨parsedTheorem, current⟩
  else 
    return ⟨{}, current⟩





structure Database where 
  data : Array ParsedTheorem

def parseDB (source : String) (start : Pos := 0) : Array ParsedTheorem := Id.run do 
  let mut current : Pos := start 
  let mut token : String := ""
  let mut db : Array ParsedTheorem := #[] 
  while current < source.endPos do 
    ⟨token, current⟩ := nextToken source current
    match getTokenKind token with 
    | .const => 
      current := forwardUntil source current "$."
    | .beginScope => 
      let mut thm : ParsedTheorem := default 
      ⟨thm, current⟩ := parseScopedPropositionalTheorem source current db 
      if !thm.proof.isEmpty then 
        db := db.push thm  
    | .symbol =>
      let prevToken := token  
      ⟨token, current⟩ := nextToken source current 
      match getTokenKind token with 
      | .provable => 
        let mut proof : ParsedProof := default 
        let mut claim : Array String := default 
        ⟨⟨_, claim, proof, _, _⟩, current⟩ := parseProvable source current db
        db := db.push { claim := claim, proof := proof, name := prevToken }
      | _ => continue 
    | _ => continue 
  return db



def testSource : String := "


imp-reflexivity $p |- ( \\imp ph0 ph0 ) $=
  ph0-is-pattern ph0-is-pattern ph0-is-pattern imp-is-pattern imp-is-pattern
  ph0-is-pattern ph0-is-pattern imp-is-pattern ph0-is-pattern ph0-is-pattern
  ph0-is-pattern imp-is-pattern ph0-is-pattern imp-is-pattern imp-is-pattern
  ph0-is-pattern ph0-is-pattern ph0-is-pattern imp-is-pattern imp-is-pattern
  ph0-is-pattern ph0-is-pattern imp-is-pattern imp-is-pattern ph0-is-pattern
  ph0-is-pattern ph0-is-pattern imp-is-pattern ph0-is-pattern proof-rule-prop-2
  ph0-is-pattern ph0-is-pattern ph0-is-pattern imp-is-pattern proof-rule-prop-1
  proof-rule-mp ph0-is-pattern ph0-is-pattern proof-rule-prop-1 proof-rule-mp
  $.



${
    rule-imp-transitivity.0 $e |- ( \\imp ph0 ph1 ) $.
    rule-imp-transitivity.1 $e |- ( \\imp ph1 ph2 ) $.
    rule-imp-transitivity $p |- ( \\imp ph0 ph2 ) $=
      ph0-is-pattern ph1-is-pattern imp-is-pattern ph0-is-pattern
      ph2-is-pattern imp-is-pattern ph0-is-pattern ph1-is-pattern
      ph2-is-pattern imp-is-pattern imp-is-pattern ph0-is-pattern
      ph1-is-pattern imp-is-pattern ph0-is-pattern ph2-is-pattern
      imp-is-pattern imp-is-pattern ph0-is-pattern ph1-is-pattern
      ph2-is-pattern proof-rule-prop-2 ph1-is-pattern ph2-is-pattern
      imp-is-pattern ph0-is-pattern ph1-is-pattern ph2-is-pattern
      imp-is-pattern imp-is-pattern ph1-is-pattern ph2-is-pattern
      imp-is-pattern ph0-is-pattern proof-rule-prop-1 rule-imp-transitivity.1
      proof-rule-mp proof-rule-mp rule-imp-transitivity.0 proof-rule-mp $.
$}

bot-elim $p |- ( \\imp \\bot ph0 ) $=
  bot-is-pattern ph0-is-pattern bot-is-pattern imp-is-pattern bot-is-pattern
  imp-is-pattern imp-is-pattern bot-is-pattern ph0-is-pattern imp-is-pattern
  bot-is-pattern ph0-is-pattern bot-is-pattern imp-is-pattern bot-is-pattern
  imp-is-pattern ph0-is-pattern imp-is-pattern imp-is-pattern bot-is-pattern
  ph0-is-pattern bot-is-pattern imp-is-pattern bot-is-pattern imp-is-pattern
  imp-is-pattern bot-is-pattern ph0-is-pattern imp-is-pattern imp-is-pattern
  bot-is-pattern ph0-is-pattern bot-is-pattern imp-is-pattern bot-is-pattern
  imp-is-pattern ph0-is-pattern proof-rule-prop-2 ph0-is-pattern bot-is-pattern
  imp-is-pattern bot-is-pattern imp-is-pattern ph0-is-pattern imp-is-pattern
  bot-is-pattern ph0-is-pattern bot-is-pattern imp-is-pattern bot-is-pattern
  imp-is-pattern ph0-is-pattern imp-is-pattern imp-is-pattern ph0-is-pattern
  bot-is-pattern imp-is-pattern bot-is-pattern imp-is-pattern ph0-is-pattern
  imp-is-pattern bot-is-pattern proof-rule-prop-1 ph0-is-pattern
  rule-imp-transitivity proof-rule-mp proof-rule-mp bot-is-pattern ph0-is-pattern
  bot-is-pattern imp-is-pattern proof-rule-prop-1 proof-rule-mp $.
"


def t := "${
    rule-imp-transitivity $p |- ( \\imp ph0 ph2 ) $=
      ph0-is-pattern ph1-is-pattern imp-is-pattern ph0-is-pattern
      ph2-is-pattern imp-is-pattern ph0-is-pattern ph1-is-pattern
      ph2-is-pattern imp-is-pattern imp-is-pattern ph0-is-pattern
      ph1-is-pattern imp-is-pattern ph0-is-pattern ph2-is-pattern
      imp-is-pattern imp-is-pattern ph0-is-pattern ph1-is-pattern
      ph2-is-pattern proof-rule-prop-2 ph1-is-pattern ph2-is-pattern
      imp-is-pattern ph0-is-pattern ph1-is-pattern ph2-is-pattern
      imp-is-pattern imp-is-pattern ph1-is-pattern ph2-is-pattern
      imp-is-pattern ph0-is-pattern proof-rule-prop-1 rule-imp-transitivity.1
      proof-rule-mp proof-rule-mp rule-imp-transitivity.0 proof-rule-mp $.
$}

bot-elim a-elim e-elim"

#eval parseDB testSource 0

#eval Substring.mk t ⟨765⟩ ⟨765 + 13⟩ |>.toString

#check List.takeWhile 


def main : IO Unit := do 
  let path : System.FilePath := "./tautologies.mm"
  let source ← IO.FS.readFile path 
  IO.println <| repr <| parseDB source |>.toList.map id

#eval main 

















section ImportingAsLeanFile 


    

end ImportingAsLeanFile


