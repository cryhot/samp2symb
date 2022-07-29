% clingo --output=smodels ltl_encoding_2.qexample.lp | qasp2qbf.py | lp2normal2 | lp2acyc | lp2sat | qasp2qbf.py --cnf2qdimacs | caqe --qdo | qasp2qbf.py --interpret
#include "ltl_encoding_2.lp".

% node(n1).
% _exists(1,node(n1)).

% % % % dummy trace
% trace(U,LEN_P,LEN_C) :- U=u1, LEN_P=0, LEN_C=1.
% val_trace(X,V, U,T)   :- U=u1, T=0,X=x1,V=false.
% val_trace(X,V, U,T)   :- U=u1, T=0,X=x2,V=true.
% % valuation
% val_node(N,V, U,T) :- U=u1, T=0,N=phi(1),V=true.
% _exists(1, val_trace(X,V, U,T)) :- U=u1, trace_T(U,T), atom(X), const(bool,V).


% %% traces %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% #const n = 3.
% node_phi(phi(1..n)).
% _exists(3,node_phi(N)) :- node_phi(N).
% % node_psi(psi(1..3)).
% % _exists(3,node_psi(N)) :- node_psi(N).

% % node(psi(1..3)).
% _exists(3,node(psi(N))) :- node(psi(N)).

% :- node_phi(N), #false: node_phi(phi(P)), phi(P)=N.

% node(N) :- node_phi(N).
% _exists(LEVEL,node(N)) :- _exists(LEVEL,node_phi(N)).
% % node(N) :- node_psi(N).
% % _exists(LEVEL,node(N)) :- _exists(LEVEL,node_psi(N)).

% :- child(N,N0), node_phi(N), not node_phi(N0).
% :- child(phi(P0),phi(P1)), not P0<P1.
% node(N, trace(bool)) :- node_phi(N).


#const n = 2.
node(phi(1..n)).
_exists(3,node(phi(P))) :- node(phi(P)).
:- child(phi(P),N0), #false: node(phi(P0)), phi(P0)=N0.                         % phi(P) can only have phi(P0) as childs
:- child(phi(P),phi(P0)), not P<P0.                                             % formula is acyclic, head is phi(1)
node(phi(P),trace(bool)) :- node(phi(P)).                                       % define typing of phi(P)

:- node(phi(_),operator(const(_),_,_),_). % do not use constants
% :- node(phi(_),operator(next,_,_),_) % do not use X



_exists(3,node(psi(P))) :- node(psi(P)).
node(psi(1),operator(atom(x0),(),trace(bool)),()).
% node(psi(1),operator(const(true),(),trace(bool)),()).
% node(psi(1),operator(const(false),(),trace(bool)),()).


% :- child(psi(P),N0), #false: node(psi(P0)), psi(P0)=N0.                         % psi(P) can only have psi(P0) as childs
% :- child(phi_limplies_psi,N0), N0!=phi(1), N0!=psi(1).                          % known childs
% :- child(psi_limplies_phi,N0), N0!=phi(1), N0!=psi(1).                          % known childs




% % #show node_phi/1.
% % #show child/2.
% % #show node/3.
% % #show node(N,OP,NODES) :
% %     % N=phi(2),
% %     node_phi(N),
% %     OPERATOR=operator(OP,TYPES,TYPE),
% %     node(N,OPERATOR,NODES).

% % #show node(N,TYPE) :
% %     N=phi(1),
% %     node(N,TYPE).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% % node_OP(N, OP) :- node(N,operator(OP,_,_),NODES).
% node_OP(N, OP, NODES) :- node(N,operator(OP,_,_),NODES).
% % :- node_OP(N, OP), node(N,operator(OP_,_,_),NODES), OP!=OP_.
% :- node_OP(N, OP, NODES), node(N,operator(OP_,_,_),NODES), OP!=OP_.
% % _exists(LEVEL,node_OP(N, OP))        :- _exists(LEVEL,node(N,_,_)), node_OP(N, OP).
% % _exists(LEVEL,node_OP(N, OP, NODES)) :- _exists(LEVEL,node(N,_,_)), node_OP(N, OP, NODES).
% % _exists(LEVEL,node_OP(N, OP, NODES)) :- _exists(LEVEL,node(N,_,_)), node_OP(N, OP, NODES), N!=phi(_).
% _exists(1,node_OP(N, OP, NODES)) :- node_OP(N, OP, NODES), N=phi(_).
% _exists(3,node_OP(N, OP, NODES)) :- node_OP(N, OP, NODES), #false: node(N_), N_=phi(_), N=N_.

% output
op(phi(P),OP,NODES) :- node(phi(P),operator(OP,_,_),NODES).
_exists(1,op(phi(P),OP,NODES)) :- op(phi(P),OP,NODES).


% :- node_OP(phi(_), const(_)).  % do not use constants
% :- node_OP(phi(_), next).  % do not use X
% % :- node_OP(phi(1), until).

% node_OP(psi(1), eventually, (psi(2),)).
% node_OP(psi(2), lnot,       (psi(3),)).
% node_OP(psi(3), atom(x0),   ()).
% node_OP(psi(1), atom(x0),   ()).


% val_node(N,V, U,T) :- U=u1, T=0,N=phi_limplies_psi,V=true.



% % #show type/1.
% % #show operator/3.

% % % dummy trace
% % trace(U,LEN_P,LEN_C) :- U=u1, LEN_P=2, LEN_C=3.
% % val_trace(X,V, U,T)   :- U=u1, T=0,X=x1,V=false.
% % val_trace(X,V, U,T)   :- U=u1, T=0,X=x2,V=true.
% % val_trace(X,V, U,T)   :- U=u1, T=1,X=x1,V=false.
% % val_trace(X,V, U,T)   :- U=u1, T=1,X=x2,V=true.
% % % cycle starts
% % val_trace(X,V, U,T)   :- U=u1, T=2,X=x1,V=false.
% % val_trace(X,V, U,T)   :- U=u1, T=2,X=x2,V=true.
% % val_trace(X,V, U,T)   :- U=u1, T=3,X=x1,V=true.
% % val_trace(X,V, U,T)   :- U=u1, T=3,X=x2,V=false.
% % val_trace(X,V, U,T)   :- U=u1, T=4,X=x1,V=true.
% % val_trace(X,V, U,T)   :- U=u1, T=4,X=x2,V=false.
% % % valuation
% % val_node(N,V, U,T) :- U=u1, T=0,N=phi(1),V=true.

% % % % % dummy trace
% % trace(U,LEN_P,LEN_C) :- U=u1, LEN_P=0, LEN_C=1.
% % val_trace(X,V, U,T)   :- U=u1, T=0,X=x1,V=false.
% % val_trace(X,V, U,T)   :- U=u1, T=0,X=x2,V=true.
% % % valuation
% % val_node(N,V, U,T) :- U=u1, T=0,N=phi(1),V=true.

% % % % % dummy trace
% % trace(U,LEN_P,LEN_C) :- U=u2, LEN_P=0, LEN_C=1.
% % val_trace(X,V, U,T)   :- U=u2, T=0,X=x1,V=false.
% % val_trace(X,V, U,T)   :- U=u2, T=0,X=x2,V=true.
% % % valuation
% % val_node(N,V, U,T) :- U=u2, T=0,N=phi(1),V=false.

% % G!x2

% % #show val_node/4.



% % trace(neg_trace,LEN_P,LEN_C) : LEN_P=1, LEN_C=1..10.
% % {trace(U,LEN_P,LEN_C) : LEN_P=1, LEN_C=1..10}=1 :- U=neg_trace.
% % val_formula(U,V) :- U=neg_trace, V=false.

atom(x0;x1).
% #const p=2.
% atom(0..p-1).


node(phi_limplies_psi).
_exists(LEVEL,node(phi_limplies_psi)) :- _exists(LEVEL,node(phi(1))).
node(phi_limplies_psi,operator(limplies,(bool,bool),bool),(phi(1),psi(1))).

#const t_all = 3.
trace_forall(all_u(LEN_P,LEN_C)) :- LEN_P=(0..t_all), LEN_C=(1..t_all), LEN_P+LEN_C<=t_all.
trace(all_u(LEN_P,LEN_C),LEN_P,LEN_C) :- trace_forall(all_u(LEN_P,LEN_C)).
_exists(9,trace_forall(U)) :- trace_forall(U).
{val(X,T)} :- atom(X), trace_forall(U), trace_T(U,T).
:- not val_trace(X,true,  U,T), trace_forall(U), trace_T(U,T), atom(X),     val(X,T).
:- not val_trace(X,false, U,T), trace_forall(U), trace_T(U,T), atom(X), not val(X,T).
_forall(2, val(X,T)) :- val(X,T).
_exists(3, val_trace(X,V, U,T)) :- val_trace(X,V, U,T), trace_forall(U).
val_node(phi_limplies_psi,true, U,0) :- trace_forall(U).


node(psi_limplies_phi).
_exists(LEVEL,node(psi_limplies_phi)) :- _exists(LEVEL,node(phi(1))).
node(psi_limplies_phi,operator(limplies,(bool,bool),bool),(psi(1),phi(1))).

#const t_any = 3.
{trace(any_u,LEN_P,LEN_C) : LEN_P=(0..t_any), LEN_C=(1..t_any), LEN_P+LEN_C<=t_any}=1.
_exists(3, val_trace(X,V, U,T)) :- val_trace(X,V, U,T), U=any_u.
val_node(psi_limplies_phi,false, U,0) :- U=any_u.


{trace(any_u2,LEN_P,LEN_C) : LEN_P=(0..t_any), LEN_C=(1..t_any), LEN_P+LEN_C<=t_any}=1.
_exists(3, val_trace(X,V, U,T)) :- val_trace(X,V, U,T), U=any_u2.
val_node(phi(1),true, U,0) :- U=any_u2.


% something is wrong with the "Next" operator


% %% constrain the formula %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% % not node_CONST(N,V) :- node(N), bool(V).
% % not node_NOT(N,N1) :- node(N), node(N1).
% % node_FINALLY(N,N1) : node(N1),N1<N :- N=n.

% % node_GLOBALLY(4,3).
% % node_UNTIL(3,1,2).
% % node_ATOM(1,x1).
% % node_ATOM(2,x2).

% % #show trace/3.
% % #show val_trace/4.


% %% END %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
