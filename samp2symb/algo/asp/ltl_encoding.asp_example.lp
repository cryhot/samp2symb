% mill -GF"*.lp" 'clingo 1 ltl_encoding_2.example.lp | tee >(! grep -e UNKNOWN -e UNSAT >/dev/null; how -b)'
#include "ltl_encoding_2.lp".




%% traces %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

node_phi(phi(1..3)).
node_psi(psi(1..3)).

:- node_phi(N), #false: node_phi(phi(P)), phi(P)=N.

node(N) :- node_phi(N).
node(N) :- node_psi(N).

node_phi(N0) :- child(N,N0), node_phi(N).
:- child(phi(P0),phi(P1)), not P0<P1.
node(N, trace(bool)) :- node_phi(N).


#show.

% #show node_phi/1.
% #show child/2.
% #show node/3.
#show node(N,OP,NODES) :
    % N=phi(2),
    node_phi(N),
    OPERATOR=operator(OP,TYPES,TYPE),
    node(N,OPERATOR,NODES).

% #show node(N,TYPE) :
%     N=phi(1),
%     node(N,TYPE).


node_OP(N, OP) :- node(N,operator(OP,_,_),NODES).
node_OP(N, OP, NODES) :- node(N,operator(OP,_,_),NODES).
:- node_OP(N, OP), node(N,operator(OP_,_,_),NODES), OP!=OP_.
:- node_OP(N, OP, NODES), node(N,operator(OP_,_,_),NODES), OP!=OP_.

:- node(phi(_),operator(const(_),_,_),_). % do not use constants
% :- node_OP(phi(_), const(_)).  % do not use constants
% :- node_OP(phi(_), next).  % do not use X
% :- node_OP(phi(3), until).


node_OP(psi(2), eventually, (psi(1),)).
node_OP(psi(1), lnot,       (psi(0),)).
node_OP(psi(0), atom(x0),   ()).

% #show type/1.
% #show operator/3.
% #show apply/3.
% #show val_node/3.

% % dummy trace
% trace(U,LEN_P,LEN_C) :- U=u1, LEN_P=2, LEN_C=3.
% val_trace(X,V, U,T)   :- U=u1, T=0,X=x1,V=false.
% val_trace(X,V, U,T)   :- U=u1, T=0,X=x2,V=true.
% val_trace(X,V, U,T)   :- U=u1, T=1,X=x1,V=false.
% val_trace(X,V, U,T)   :- U=u1, T=1,X=x2,V=true.
% % cycle starts
% val_trace(X,V, U,T)   :- U=u1, T=2,X=x1,V=false.
% val_trace(X,V, U,T)   :- U=u1, T=2,X=x2,V=true.
% val_trace(X,V, U,T)   :- U=u1, T=3,X=x1,V=true.
% val_trace(X,V, U,T)   :- U=u1, T=3,X=x2,V=false.
% val_trace(X,V, U,T)   :- U=u1, T=4,X=x1,V=true.
% val_trace(X,V, U,T)   :- U=u1, T=4,X=x2,V=false.
% % valuation
% val_node(N,V, U,T) :- U=u1, T=0,N=phi(1),V=true.

% % dummy trace
trace(U,LEN_P,LEN_C) :- U=u1, LEN_P=0, LEN_C=1.
val_trace(X,V, U,T)   :- U=u1, T=0,X=x1,V=false.
val_trace(X,V, U,T)   :- U=u1, T=0,X=x2,V=false.
_exists(3, val_trace(X,V, U,T)) :- U=u1, val_trace(X,V, U,T).
% valuation
val_node(N,V, U,T) :- U=u1, T=0,N=phi(1),V=true.

% % % dummy trace
% trace(U,LEN_P,LEN_C) :- U=u2, LEN_P=0, LEN_C=1.
% val_trace(X,V, U,T)   :- U=u2, T=0,X=x1,V=false.
% val_trace(X,V, U,T)   :- U=u2, T=0,X=x2,V=true.
% _exists(3, val_trace(X,V, U,T)) :- U=u2, val_trace(X,V, U,T).
% % valuation
% val_node(N,V, U,T) :- U=u2, T=0,N=phi(1),V=false.

% G!x2

% #show val_node/4.



% trace(neg_trace,LEN_P,LEN_C) : LEN_P=1, LEN_C=1..10.
% {trace(U,LEN_P,LEN_C) : LEN_P=1, LEN_C=1..10}=1 :- U=neg_trace.
% val_formula(U,V) :- U=neg_trace, V=false.


%% constrain the formula %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% :- node(phi(_),operator(finally,_,_),_). % do not use constants
% :- node(phi(_),operator(globally,_,_),_). % do not use constants
% :- node(phi(_),operator(until,_,_),_). % do not use constants
% :- node(phi(_),operator(lnot,_,_),_). % do not use constants
% :- node(phi(_),operator(atom(x2),_,_),_). % do not use constants
% :- node(phi(_),operator(lequiv,_,_),_). % do not use constants
% :- node(phi(_),operator(limplies,_,_),_). % do not use constants


% #show next/3.


% not node_CONST(N,V) :- node(N), bool(V).
% not node_NOT(N,N1) :- node(N), node(N1).
% node_FINALLY(N,N1) : node(N1),N1<N :- N=n.

% node_GLOBALLY(4,3).
% node_UNTIL(3,1,2).
% node_ATOM(1,x1).
% node_ATOM(2,x2).

% #show trace/3.
% #show val_trace/4.



%% END %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
