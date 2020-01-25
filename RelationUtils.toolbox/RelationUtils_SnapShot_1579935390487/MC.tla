---- MODULE MC ----
EXTENDS RelationUtils, TLC

\* Constant expression definition @modelExpressionEval
const_expr_157993538847168000 == 
SeqToRel(<<1, 2>>)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157993538847168000>>)
----

=============================================================================
\* Modification History
\* Created Sat Jan 25 14:56:28 CST 2020 by hengxin
