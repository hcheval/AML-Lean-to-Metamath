
$[ mm/matching-logic.mm $]
$v  x9 $v.

x9-is-evar $f #ElementVariable x9 $.

ML.Meta.Tests.formationExists0 $p |- ( \imp ( \exist x9 x9 ) ( \imp ( \exist x9 x9 ) ( \exist x9 x9 ) ) ) $=  x9-is-evar  x9-is-evar var-is-pattern exists-is-pattern  x9-is-evar  x9-is-evar var-is-pattern exists-is-pattern proof-rule-prop-1 $.
