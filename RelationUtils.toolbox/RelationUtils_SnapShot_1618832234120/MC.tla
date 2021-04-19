---- MODULE MC ----
EXTENDS RelationUtils, TLC

\* Constant expression definition @modelExpressionEval
const_expr_161883223210620000 == 
CyclicTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161883223210620000>>)
----

=============================================================================
\* Modification History
\* Created Mon Apr 19 19:37:12 CST 2021 by hengxin
