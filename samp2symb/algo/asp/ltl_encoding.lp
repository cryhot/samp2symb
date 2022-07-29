% LTL encoding

%% trace definition %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
node(N) :- (N,)=().             % node/1: DAG nodes (empty for now)
% formula(F,N) :- (F,N,)=().

%% trace definition %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
atom(X) :- (X,)=().             % atom/1: atomic propositions (empty for now)
_exists(9,atom(X)) :- atom(X).

trace(U,LEN_P,LEN_C) :- (U,LEN_P,LEN_C,)=().
trace(U,LEN) :- trace(U,LEN_P,LEN_C), LEN=LEN_P+LEN_C.
trace(U) :- trace(U,_,_).

trace_T(U,T) :- trace(U,LEN_P,LEN_C), T=0..LEN_P+LEN_C-1.
cycle_T(U,T) :- trace(U,LEN_P,LEN_C), T=LEN_P..LEN_P+LEN_C-1.
future(U,T1,T2) :- trace_T(U,T1), trace_T(U,T2), T1<=T2.
future(U,T1,T2) :- cycle_T(U,T1), cycle_T(U,T2).
future(U,T1,T2,T3) :- trace_T(U,T1), trace_T(U,T2), trace_T(U,T3), T1<=T2, T2<=T3.
future(U,T1,T2,T3) :- cycle_T(U,T1), cycle_T(U,T2), cycle_T(U,T3), T1>T3, T1<=T2.
future(U,T1,T2,T3) :- cycle_T(U,T1), cycle_T(U,T2), cycle_T(U,T3), T1>T3, T2<=T3.
next(U,T1,T2) :- trace_T(U,T1), trace_T(U,T2), T1+1=T2.
next(U,T1,T2) :- trace(U,LEN_P,LEN_C), T1=LEN_P+LEN_C-1, T2=LEN_P.
% these might not be strong enough...

_exists(9,trace(U)) :- trace(U).
_exists(LEVEL,trace(U,LEN_P,LEN_C)) :- _exists(LEVEL,trace(U)), trace(U,LEN_P,LEN_C).
_exists(LEVEL,trace(U,LEN)) :- _exists(LEVEL,trace(U,_,_)), trace(U,LEN).
_exists(LEVEL,trace_T(U,T)) :- _exists(LEVEL,trace(U,_,_)), trace_T(U,T).
_exists(LEVEL,cycle_T(U,T)) :- _exists(LEVEL,trace(U,_,_)), cycle_T(U,T).
_exists(LEVEL,future(U,T1,T2)) :- _exists(LEVEL,trace(U,_,_)), future(U,T1,T2).
_exists(LEVEL,future(U,T1,T2,T3)) :- _exists(LEVEL,trace(U,_,_)), future(U,T1,T2,T3).
_exists(LEVEL,next(U,T1,T2)) :- _exists(LEVEL,trace(U,_,_)), next(U,T1,T2).

{val_trace(X,V, U,T) : const(bool,V)}=1 :- trace_T(U,T), atom(X).  % single valuation

{val_node(N,V, U,T) : const(TYPE,V)}=1 :- trace_T(U,T), node(N,trace(TYPE)).  % single valuation
val_node(N,V, U) :- val_node(N,V, U,T), T=0.
_exists(LEVEL,val_node(N,V, U,T)) :- _exists(LEVEL,val_trace(_,_, U,T)), val_node(N,V, U,T).
_exists(LEVEL,val_node(N,V, U)) :- _exists(LEVEL,val_node(N,_, U,_)), val_node(N,V, U).


% formula()
% {val_formula(U,N, V) : const(bool,V)}=1 :- trace(U).  % single valuation
% :- val_formula(U, V), val_node(N,V_, U,T), T=0, N=n, V!=V_.

atom(X) :- val_trace(X,V, U,T). % register as an atom

%% defines types %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

#include "bool.lp".
% #include "types.lp".
type_atomic(bool).
_exists(9,type_atomic(TYPE)) :- type_atomic(TYPE).
% type(TYPE) :- type_atomic(TYPE).

% %% time dimention
% type(sequ(TYPE)) :- type_atomic(TYPE).
type(trace(TYPE)) :- type_atomic(TYPE).

% %% trace dimention
% type(trace).
% type(prop(TYPE)) :- type_atomic(TYPE).
% type(sequ(prop(TYPE))) :- type_atomic(TYPE).
operator(atom(X), (), trace(bool)) :- atom(X).

operator(now, (trace(TYPE),), TYPE) :- type(trace(TYPE)).
% apply(now, (SIG1,), SIG). % is this possible?
operator(finally, (trace(bool),), trace(bool)).
operator(globally, (trace(bool),), trace(bool)).
operator(until, (trace(bool),trace(bool),), trace(bool)).
operator(next, (trace(bool),), trace(bool)).

operator(val, (prop(TYPE),), TYPE) :- type(prop(TYPE)). %?

% operator(lift(OP), TRACE_TYPES, trace(TYPE)) :- operator(OP, TYPES, TYPE), % lift
operator(OP, TRACE_TYPES, trace(TYPE)) :- operator(OP, TYPES, TYPE), % lift
(TYPES,TRACE_TYPES)=(
    ((           ), (                         ));
    ((TYPE1,     ), (trace(TYPE1),            ));
    ((TYPE1,TYPE2), (trace(TYPE1),trace(TYPE2)));
),
type(trace(TYPE)), type(trace(TYPE1)), type(trace(TYPE2)).




%% defines node operation %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% node type
{
    node(N,TYPE) : type(TYPE);
    #false
}=1 :-
node(N).

node(N) :- node(N,_).
_exists(LEVEL,node(N)) :- _exists(LEVEL,node(N,_)).
_exists(LEVEL,node(N,OPERATOR,NODES)) :- _exists(LEVEL,node(N)), node(N,OPERATOR,NODES).

%% node operator
{
    node(N,OPERATOR,NODES)
    :
    operator(OP,TYPES,TYPE), OPERATOR=operator(OP,TYPES,TYPE),
    (NODES, TYPES)=(
        ((      ), (            ));
        ((N1,   ), (TYPE1,      ));
        ((N1,N2,), (TYPE1,TYPE2,));
    ),
    node(N1,TYPE1), node(N2,TYPE2)
}=1 :-
node(N,TYPE).
% TODO: duplicate {...}=1 with weaker constraints, to eliminates impossible nodes.

% node(N,TYPE) :- node(N,OPERATOR,NODES), OPERATOR=operator(_,_,TYPE).
node(N) :- node(N,_,_).
:- node(N,OPERATOR,NODES), OPERATOR=operator(_,_,TYPE), not node(N,TYPE).
_exists(LEVEL,node(N,TYPE)) :- _exists(LEVEL,node(N,_,_)), node(N,TYPE).


child(N,N0) :-
    node(N,OPERATOR,NODES),
    NODES=(
        (N0,  );
        (N0,_,); (_,N0,)
    ),
    node(N0,_).
:- child(N,N0),
    #false:
        node(N,OPERATOR,NODES),
        NODES=(
            (N0,  );
            (N0,_,); (_,N0,)
        ),
        node(N0,_).
_exists(LEVEL,child(N,N0)) :- _exists(LEVEL,node(N)), child(N,N0).

% :- node(N0,TYPE0), child(_,N0,TYPE0_), TYPE0!=TYPE0_.
% child(N,N0) :- child(N,N0,_).

atom(X) :- node(_,operator(atom(X),_,_),_).


%% LTL semantics %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% generic operator:
% - no time, prop or any other dimention involved,
% - apply(OP, VALUES, ANS) is defined.
#false :-
    node(N,OPERATOR,NODES), OPERATOR=operator(OP,_,_),
    val_node(N,V, U,T),
    (NODES, VALUES)=(
        ((      ), (      ));
        ((N1,   ), (V1,   ));
        ((N1,N2,), (V1,V2,));
    ),
    val_node(N1,V1, U,T), val_node(N2,V2, U,T),
    apply(OP, VALUES, ANS),
    V!=ANS.

%% atoms
#false :-
    node(N,OPERATOR,()), OPERATOR=operator(atom(X),_,_),
    val_node(N,V, U,T),
    val_trace(X,V_, U,T),
    V!=V_.


%% finally operator
#false :-
    node(N,OPERATOR,(N1,)), OPERATOR=operator(finally,_,_),
    val_node(N,V, U,T),
    val_node(N1,true, U,T1), future(U,T,T1),
    V!=true.
#false :-
    node(N,OPERATOR,(N1,)), OPERATOR=operator(finally,_,_),
    val_node(N,V, U,T),
    #false: val_node(N1,true, U,T1), future(U,T,T1);
    V!=false.

%% globally operator
#false :-
    node(N,OPERATOR,(N1,)), OPERATOR=operator(globally,_,_),
    val_node(N,V, U,T),
    val_node(N1,false, U,T1), future(U,T,T1),
    V!=false.
#false :-
    node(N,OPERATOR,(N1,)), OPERATOR=operator(globally,_,_),
    val_node(N,V, U,T),
    #false: val_node(N1,false, U,T1), future(U,T,T1);
    V!=true.

%% until operator
#false :- % true if V2 becomes true without V1 becomming false earlier
    node(N,OPERATOR,(N1,N2,)), OPERATOR=operator(until,_,_),
    val_node(N,V, U,T),
    #false: val_node(N1,false, U,T1), future(U,T,T1,T2), T1!=T2;
    val_node(N2,true, U,T2), future(U,T,T2),
    V!=true.
#false :- % false if V1 becomes false without V2 becomming true earlier
    node(N,OPERATOR,(N1,N2,)), OPERATOR=operator(until,_,_),
    val_node(N,V, U,T),
    val_node(N1,false, U,T1), future(U,T,T1),
    #false: val_node(N2,true, U,T2), future(U,T,T2,T1);
    V!=false.
#false :- % false if V2 never true (strong until).
    node(N,OPERATOR,(N1,N2,)), OPERATOR=operator(until,_,_),
    val_node(N,V, U,T),
    #false: val_node(N2,true, U,T2), future(U,T,T2);
    V!=false.

%% next operator
#false :-
    node(N,OPERATOR,(N1,)), OPERATOR=operator(next,_,_),
    val_node(N,V, U,T),
    val_node(N1,V1, U,T1), next(U,T,T1),
    V!=V1.
#false :- % if no next timestep
    node(N,OPERATOR,(N1,)), OPERATOR=operator(next,_,trace(bool)),
    val_node(N,V, U,T),
    #false: val_node(N1,V1, U,T1), next(U,T,T1),
    V!=false.



%% LTL semantics %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% #const n = 4.
% node(phi(1..n)).


%% LTL semantics %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% :- val_node(U,T,N, V), node_CONST(N,V_), V!=V_.
% :- val_node(U,T,N, V), node_ATOM(N,X), val_trace(U,T,X, V_), V!=V_.
% :- val_node(U,T,N, V), node_NOT(N,N1),        val_node(U,T,N1, V1),                       lnot(V_, V1),        V!=V_.
% :- val_node(U,T,N, V), node_OR(N,N1,N2),      val_node(U,T,N1, V1), val_node(U,T,N2, V2), lor(V_, V1,V2),      V!=V_.
% :- val_node(U,T,N, V), node_AND(N,N1,N2),     val_node(U,T,N1, V1), val_node(U,T,N2, V2), land(V_, V1,V2),     V!=V_.
% :- val_node(U,T,N, V), node_IMPLIES(N,N1,N2), val_node(U,T,N1, V1), val_node(U,T,N2, V2), limplies(V_, V1,V2), V!=V_.
% :- val_node(U,T,N, V), node_FINALLY(N,N1),          val_node(U,T1,N1,true), future(U,T,T1),  V!=true.
% :- val_node(U,T,N, V), node_FINALLY(N,N1),  #false: val_node(U,T1,N1,true), future(U,T,T1);  V!=false.
% % :- val_node(U,T,N, V), node_FINALLY(N,N1), {val_node(U,T1,N1,true): future(U,T,T1)}>0, V!=true.
% % :- val_node(U,T,N, V), node_FINALLY(N,N1), {val_node(U,T1,N1,true): future(U,T,T1)}=0, V!=false.
% :- val_node(U,T,N, V), node_GLOBALLY(N,N1),          val_node(U,T1,N1,false), future(U,T,T1),  V!=false.
% :- val_node(U,T,N, V), node_GLOBALLY(N,N1),  #false: val_node(U,T1,N1,false), future(U,T,T1);  V!=true.
% % :- val_node(U,T,N, V), node_GLOBALLY(N,N1), {val_node(U,T1,N1,false): future(U,T,T1)}>0, V!=false.
% % :- val_node(U,T,N, V), node_GLOBALLY(N,N1), {val_node(U,T1,N1,false): future(U,T,T1)}=0, V!=true.
% :- val_node(U,T,N, V), node_UNTIL(N,N1,N2),  #false: val_node(U,T1,N1,false), future(U,T,T1,T2), T1!=T2;  val_node(U,T2,N2,true), future(U,T,T2),  V!=true.
% :- val_node(U,T,N, V), node_UNTIL(N,N1,N2),  val_node(U,T1,N1,false), future(U,T,T1),  #false: val_node(U,T2,N2,true), future(U,T,T2,T1);  V!=false.
% :- val_node(U,T,N, V), node_UNTIL(N,N1,N2),  #false: val_node(U,T2,N2,true), future(U,T,T2);  V!=false.
% :- val_node(U,T,N, V), node_NEXT(N,N1), val_node(U,T1,N1, V1), next(U,T,T1), V!=V1.



% value uniqueness
% not val_trace(U,T,X,V2) :- val_trace(U,T,X,V), bool(V2), V2!=V.
% not val_node(U,T,N,V2) :- val_node(U,T,N,V), bool(V2), V2!=V.
% :- val_node(U,T,N,V), true(V),false(V).


%% traces %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% % % dummy trace
% trace(U,LEN_P,LEN_C) :- U=u1, LEN_P=2, LEN_C=3.
% val_trace(U,T,X,V)   :- U=u1, T=0,X=x1,V=false.
% val_trace(U,T,X,V)   :- U=u1, T=0,X=x2,V=true.
% val_trace(U,T,X,V)   :- U=u1, T=1,X=x1,V=false.
% val_trace(U,T,X,V)   :- U=u1, T=1,X=x2,V=true.
% % cycle starts
% val_trace(U,T,X,V)   :- U=u1, T=2,X=x1,V=false.
% val_trace(U,T,X,V)   :- U=u1, T=2,X=x2,V=true.
% val_trace(U,T,X,V)   :- U=u1, T=3,X=x1,V=true.
% val_trace(U,T,X,V)   :- U=u1, T=3,X=x2,V=false.
% val_trace(U,T,X,V)   :- U=u1, T=4,X=x1,V=true.
% val_trace(U,T,X,V)   :- U=u1, T=4,X=x2,V=false.
% val_formula(U,V) :- U=u1, V=false.

% trace(neg_trace,LEN_P,LEN_C) : LEN_P=1, LEN_C=1..10.
% {trace(U,LEN_P,LEN_C) : LEN_P=1, LEN_C=1..10}=1 :- U=neg_trace.
% val_formula(U,V) :- U=neg_trace, V=false.


%% constrain the formula %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% not node_CONST(N,V) :- node(N), const(bool,V).
% not node_NOT(N,N1) :- node(N), node(N1).
% node_FINALLY(N,N1) : node(N1),N1<N :- N=n.

% node_GLOBALLY(4,3).
% node_UNTIL(3,1,2).
% node_ATOM(1,x1).
% node_ATOM(2,x2).

% #show trace/3.
% #show val_trace/4.

%% quantifiers %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% _exists(9,trace(U)) :- trace(U).
% _exists(9,trace(U)) :- trace(U).



%% END %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
