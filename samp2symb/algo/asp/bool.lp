
#include "types.lp".

type(bool).
const(bool, (true;false)).

operator(lnot, (bool,), bool).
#false :- apply(lnot, (A,), ANS), ANS!=false,
    A=true.
#false :- apply(lnot, (A,), ANS), ANS!=true,
    A=false.

operator(lor, (bool,bool,), bool).
#false :- apply(lor, (A,B,), ANS), ANS!=false,
    A=false, B=false.
#false :- apply(lor, (A,B,), ANS), ANS!=true,
    #false: A=false, B=false.

operator(land, (bool,bool,), bool).
#false :- apply(land, (A,B,), ANS), ANS!=X,
    apply(lnot, (A,), NOT_A),
    apply(lnot, (B,), NOT_B),
    apply(lor, (NOT_A,NOT_B,), NOT_X),
    apply(lnot, (NOT_X,), X).

operator(limplies, (bool,bool,), bool).
#false :- apply(limplies, (A,B,), ANS), ANS!=X,
    apply(lnot, (A,), NOT_A),
    apply(lor, (NOT_A,B,), X).

operator(lequiv, (bool,bool,), bool).
#false :- apply(lequiv, (A,B,), ANS), ANS!=X,
    apply(limplies, (A,B,), A_B),
    apply(limplies, (B,A,), B_A),
    apply(land, (A_B,B_A,), X).


% {apply(OP, VALUES, V) : const(T,V)}<=1 :-  % single valuation
{apply(OP, VALUES, V) : const(T,V)}=1 :-  % forces evaluation
    operator(OP, TYPES, T),
    (TYPES, VALUES)=(
        ((      ), (      ));
        ((T1,   ), (V1,   ));
        ((T1,T2,), (V1,V2,));
        % expand this to take into account greater arity operators.
    ),
    const(T1,V1), const(T2,V2),
    T=bool, T1=bool, T2=bool.