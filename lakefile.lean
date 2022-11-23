import Lake
open Lake DSL

package mMExtraction {
  -- add package configuration options here
}

@[default_target]
lean_lib MMExtraction {
  -- add library configuration options here
}

-- @[default_target]
-- lean_exe mmextraction {
--   root := `Main
-- }

require MatchingLogic from  
  git "https://gitlab.com/ilds/aml-lean/MatchingLogic.git"@"propositional-axioms"

