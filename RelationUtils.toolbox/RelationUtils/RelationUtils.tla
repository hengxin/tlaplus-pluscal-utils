------------------------------- MODULE RelationUtils -------------------------------
(*
Relation related operators.
*)
EXTENDS Naturals, Sequences, FunctionUtils
----------------------------------------------------------------------------
Dom(R) == {a : <<a, b>> \in R} \* domain of relation R

Ran(R) == {b : <<a, b>> \in R} \* range of relation R

Support(R) == Dom(R) \cup Ran(R) \* support of relation R

Inverse(R) == {<<b, a>> : <<a, b>> \in R} \* inverse of relation R

GT(R, a) == {b \in Ran(R): <<a, b>> \in R}

LT(R, b) == {a \in Dom(R): <<a, b>> \in R}

R | S == R \cap S \times S \* restriction of R on S

Reflexive(S, R) == \forall a \in S: <<a, a>> \in R \* is R reflexive?
    
Transitive(R) == \* is R transitive?
    LET S == Support(R)     
    IN  \forall a, b, c \in S: 
            (<<a, b>> \in R /\ <<b, c>> \in R) => <<a, c>> \in R
    
R ** T == \* composition of R and T
    LET SR == Support(R) 
        ST == Support(T) 
    IN  {<<r, t>> \in SR \X ST : 
            \E s \in SR \cap ST : (<<r, s>> \in R) /\ (<<s, t>> \in T)}

TC(R) == \* transitive closure of R; see https://github.com/jameshfisher/tlaplus/blob/master/examples/TransitiveClosure/TransitiveClosure.tla
    LET S == Support(R) 
        RECURSIVE TCR(_)
        TCR(T) == IF T = {} 
                  THEN R
                  ELSE LET r == CHOOSE s \in T : TRUE
                           RR == TCR(T \ {r})
                       IN  RR \cup {<<s, t>> \in S \X S : 
                                      <<s, r>> \in RR /\ <<r, t>> \in RR}
    IN  TCR(S)
  
(* 
Transitive closure of relation R.
RECURSIVE TC(_)
TC(R) == 
    LET RR == R ** R 
    IN  IF RR \subseteq R THEN R ELSE TC(R \cup RR) 
*)

(*
Example:
SeqToRel(<<1, 2, 3>>) = {<<1, 2>>, <<1, 3>>, <<2, 3>>}
*)
SeqToRel(s) == \* transform a (total order) sequence to a relation
    LET RECURSIVE SeqRel(_, _)
        SeqRel(seq, rel) ==
            IF Len(seq) <= 1
            THEN rel
            ELSE LET h == Head(seq)
                     t == Tail(seq)
                 IN  SeqRel(t, rel \cup {<<h, r>> : r \in Range(t)})
    IN  SeqRel(s, {})
=============================================================================
\* Modification History
\* Last modified Sat Jan 25 14:54:40 CST 2020 by hengxin
\* Created Tue Sep 18 19:16:04 CST 2018 by hengxin