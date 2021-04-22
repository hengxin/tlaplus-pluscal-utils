---- MODULE MC ----
EXTENDS RelationUtils, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1619073817966298000 == 
IsStrictTotalOrderTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619073817966298000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1619073817966299000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1619073817966300000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Thu Apr 22 14:43:37 CST 2021 by hengxin
