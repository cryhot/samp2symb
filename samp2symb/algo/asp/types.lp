
%% types structure %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

type(TYPE)                      % type/1: set of types
:- (TYPE,)=().                  % (empty for now)

const(TYPE, VALUE)              % const/2: members of that type
:- (TYPE, VALUE,)=().           % (empty for now)

operator(OP, TYPES, TYPE)       % operator/3: operator with it's signature (tuple of input types, and output type)
:- (OP, TYPES, TYPE,)=().       % (empty for now)

apply(OP, VALUES, VALUE)        % apply/3: apply an operator (tuple of input values, and output value)
:- (OP, VALUES, VALUE,)=().     % (empty for now)

%% quantifiers %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
_exists(9,type(TYPE)) :- type(TYPE).
_exists(9,const(TYPE, VALUE)) :- const(TYPE, VALUE).
_exists(9,operator(OP, TYPES, TYPE)) :- operator(OP, TYPES, TYPE).
_exists(9,apply(OP, VALUES, VALUE)) :- apply(OP, VALUES, VALUE).

%% others %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


operator(const(VALUE), (), TYPE) :- const(TYPE, VALUE).
:- apply(const(VALUE), (), ANS), ANS!=VALUE, const(TYPE, VALUE).
% apply(const(VALUE), (), VALUE) :- const(VALUE, TYPE).


{apply(OP, VALUES, V) : const(T,V)}<=1 :-  % single valuation
% {apply(OP, VALUES, V) : const(T,V)}=1 :-  % forces evaluation
operator(OP, TYPES, T),
(TYPES, VALUES)=(
    ((      ), (      ));
    ((T1,   ), (V1,   ));
    ((T1,T2,), (V1,V2,));
    % expand this to take into account greater arity operators.
),
const(T1,V1), const(T2,V2).

% #show apply/3.
% #show apply(OP, VALUES, V) : apply(OP, VALUES, V), operator(OP, TYPES, TYPE).
% #show.