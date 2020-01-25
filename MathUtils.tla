---------------------- MODULE AdditionalMathOperators ----------------------
EXTENDS Naturals

PosInt == Nat \ {0}

Min(x, y) == IF x <= y THEN x ELSE y
Max(x, y) == IF x <= y THEN y ELSE x

SetMin(s) == CHOOSE a \in S: \A b \in S: a <= b
SetMax(s) == CHOOSE a \in S: \A b \in S: b <= a
=============================================================================
\* Modification History
\* Last modified Sat Jan 25 17:05:44 CST 2020 by hengxin
\* Created Fri Jul 06 13:08:50 CST 2018 by hengxin