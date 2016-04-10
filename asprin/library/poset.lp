#program preference(poset).

%
% qualitative preferences
%

required(P)       :- preference(P,poset), required(P,_).
required(P,noteq) :- preference(P,poset), required(P,X), X != eq.

poset(P,X) :- preference(P,poset), required(P),
              preference(P,_,_,for(X),_).

poset(P,X,Y) :- preference(P,poset), required(P,noteq),
                preference(P,I,1,for(X),_), preference(P,I,2,for(Y),_).

% transitive closure
poset(P,X,Y) :- preference(P,poset), required(P,noteq),
                poset(P,X,Z), poset(P,Z,Y).

% better

better(P,X) :- preference(P,poset), required(P,better), 
               poset(P,X), holds(X), not holds'(X).

notbetter(P) :- preference(P,poset), required(P,better),
                poset(P,X), not holds(X), holds'(X),
                not better(P,Y) : poset(P,Y,X).

better(P) :- preference(P,poset), required(P,better),
             1 #sum { 1: better(P,X) }, not notbetter(P).

% bettereq
required(P,eq)        :- preference(P,poset), required(P,bettereq).
required(P,better)    :- preference(P,poset), required(P,bettereq).
bettereq(P)  :- preference(P,poset), required(P,bettereq),
                1 #sum { eq(P), better(P) }.

% eq
eq(P) :- preference(P,poset), required(P,eq),
         holds(X) : poset(P,X), holds'(X);
         not holds(X) : poset(P,X), not holds'(X).


% worseeq
required(P,eq)    :- preference(P,poset), required(P,worseeq).
required(P,worse) :- preference(P,poset), required(P,worseeq).
worseeq(P)  :- preference(P,poset), required(P,worseeq),
               1 #sum { eq(P), worse(P) }.


% worse
worse(P,X) :- preference(P,poset), required(P,worse),
              poset(P,X), holds'(X), not holds(X).

notworse(P) :- preference(P,poset), required(P,worse),
               poset(P,X), not holds'(X), holds(X),
		       not worse(P,Y) : poset(P,Y,X).

worse(P) :- preference(P,poset), required(P,worse),
            1 #sum { 1: worse(P,X) }, not notworse(P).

% unc
required(P,bettereq) :- preference(P,poset), required(P,unc).
required(P,worseeq)  :- preference(P,poset), required(P,unc).
unc(P) :- preference(P,poset), required(P,unc),
          not bettereq(P), not worseeq(P).

%%%
%%% _error/1
%%%

_error(M) :- M = @cat("poset: In preference element ",N," of preference statement ",P,", naming atom 'name(",X,")' is not allowed."), 
             preference(P,poset), 
             preference(P,(N,_),_,name(X),_).

_error(M) :-  M = @cat("poset: In preference element ",N," of preference statement ",P,", weight '",W,"' appearing in weighted boolean formula '",W,"::",X,"' is not allowed."),
              preference(P,poset), 
              preference(P,(N,_),_,X,W), W != ().

_error(M) :- M = @cat("poset: In preference element ",N," of preference statement ",P,", condition '",X,"' is not allowed."),
             preference(P,poset), 
             preference(P,(N,_),0,for(X),_).

_error(M) :- M = @cat("poset: In preference element ",N," of preference statement ",P,", element '",X,"' is not allowed."),
             preference(P,poset), 
             preference(P,(N,_),R,for(X),_), R > 2.


