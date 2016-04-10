#program preference(superset).
:- not better(P), optimize(P).
better(P) :- preference(P,superset); optimize(P); 
             holds(X) : preference(P,_,_,for(X),_), holds'(X);
             1 #sum { 1 : holds(X), not holds'(X), preference(P,_,_,for(X),_)}.
