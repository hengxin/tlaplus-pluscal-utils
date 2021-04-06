---- MODULE MC ----
EXTENDS RelationUtils, TLC

\* Constant expression definition @modelExpressionEval
const_expr_16177117867299000 == 
AllLinearExtensions(rel1, set1) = LinearExtensions(rel1, set1)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_16177117867299000>>)
----

=============================================================================
\* Modification History
\* Created Tue Apr 06 20:23:06 CST 2021 by hengxin
