#program preference(subset).
:- not better(P), optimize(P).
better(P) :- preference(P,subset); optimize(P); 
             not holds(X) : preference(P,_,_,for(X),_), not holds'(X);
             1 #sum { 1 : not holds(X), holds'(X), preference(P,_,_,for(X),_)}.
