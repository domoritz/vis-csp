#program preference(poset).
:- not better(P), optimize(P).

preference(P,for(X)) :- preference(P,poset),
                        preference(P,_,_,for(X),_).

preference(P,for(X),for(Y)) :- preference(P,poset), 
                               preference(P,I,1,for(X),_), preference(P,I,2,for(Y),_).

% better

better(P,for(X)) :- preference(P,poset), 
                    preference(P,for(X)), holds(X), not holds'(X).

notbetter(P) :- preference(P,poset),
                preference(P,for(X)), not holds(X), holds'(X),
                not better(P,for(Y)) : preference(P,for(Y),for(X)).

better(P) :- preference(P,poset),
                1 #sum { 1: better(P,for(X)) }, not notbetter(P).

