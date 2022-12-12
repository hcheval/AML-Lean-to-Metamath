
$[ mm/matching-logic.mm $]
$v  ph19 ph20 ph21 $v.

ph19-is-pattern $f #Pattern ph19 $.
ph20-is-pattern $f #Pattern ph20 $.
ph21-is-pattern $f #Pattern ph21 $.
${
_uniq.24 $e ( \imp ph20 ph21 ) $.
_uniq.23 $e ( \imp ph19 ph20 ) $.
_uniq.22 $e ph19 $.
ML.Meta.Tests.modusPonensTest4 $p |- ph21 $=  ph20-is-pattern  ph21-is-pattern  ph19-is-pattern  ph20-is-pattern  _uniq.22  _uniq.23 proof-rule-mp  _uniq.24 proof-rule-mp $.
$}