---- MODULE MC ----
EXTENDS RelationUtils, TLC

\* Constant expression definition @modelExpressionEval
const_expr_157993539450869000 == 
SeqToRel(<<1>>)
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_157993539450869000>>)
----

=============================================================================
\* Modification History
\* Created Sat Jan 25 14:56:34 CST 2020 by hengxin
