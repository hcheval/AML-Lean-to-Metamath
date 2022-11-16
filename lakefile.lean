import Lake
open Lake DSL

package mMExtraction {
  -- add package configuration options here
}

@[default_target]
lean_lib MMExtraction {
  -- add library configuration options here
}

require MatchingLogic from  
  git "https://gitlab.com/ilds/aml-lean/MatchingLogic.git"@"no-wf"

-- @[default_target]
-- lean_exe mMExtraction {
--   root := `Main
-- }
