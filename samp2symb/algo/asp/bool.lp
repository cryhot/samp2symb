
#include "types.lp".

type(bool).
const(bool, (true;false)).

operator(lnot, (bool,), bool).
:- apply(lnot, (A,), ANS), ANS!=false, A=true.
:- apply(lnot, (A,), ANS), ANS!=true,  A=false.

operator(lor, (bool,bool,), bool).
:- apply(lor, (A,B,), ANS), ANS!=false,         A=false, B=false.
:- apply(lor, (A,B,), ANS), ANS!=true,  #false: A=false, B=false.

operator(land, (bool,bool,), bool).
:- apply(land, (A,B,), ANS), ANS!=X,
apply(lnot, (A,), NOT_A),
apply(lnot, (B,), NOT_B),
apply(lor, (NOT_A,NOT_B,), NOT_X),
apply(lnot, (NOT_X,), X).

operator(limplies, (bool,bool,), bool).
:- apply(limplies, (A,B,), ANS), ANS!=X,
apply(lnot, (A,), NOT_A),
apply(lor, (NOT_A,B,), X).

operator(lequiv, (bool,bool,), bool).
:- apply(lequiv, (A,B,), ANS), ANS!=X,
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