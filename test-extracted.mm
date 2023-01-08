
$[ matching-logic.mm $]

$v  _x0 $.
$v _xX $. 

_x0-is-element-var $f #ElementVariable _x0 $.
_xX-is-var $f #Variable _xX $. 

existence-test $p |- ( \exists _x0 _x0 ) $=  _x0-is-element-var proof-rule-existence $.

fresh-test $p #Fresh xX \bot $= ? $. 