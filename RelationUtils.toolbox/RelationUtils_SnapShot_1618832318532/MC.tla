---- MODULE MC ----
EXTENDS RelationUtils, TLC

\* Constant expression definition @modelExpressionEval
const_expr_161883231651921000 == 
CyclicTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_161883231651921000>>)
----

=============================================================================
\* Modification History
\* Created Mon Apr 19 19:38:36 CST 2021 by hengxin
