---- MODULE MC ----
EXTENDS RelationUtils, TLC

\* Constant expression definition @modelExpressionEval
const_expr_1619074093840304000 == 
IsStrictTotalOrderTest
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1619074093840304000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_1619074093840305000 ==
FALSE/\x = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_1619074093840306000 ==
FALSE/\x' = x
----
=============================================================================
\* Modification History
\* Created Thu Apr 22 14:48:13 CST 2021 by hengxin
