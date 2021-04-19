---- MODULE MC ----
EXTENDS RelationUtils, TLC

\* Constant expression definition @modelExpressionEval
const_expr_161883232577922000 == 
CyclicTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161883232577922000>>)
----

=============================================================================
\* Modification History
\* Created Mon Apr 19 19:38:45 CST 2021 by hengxin
