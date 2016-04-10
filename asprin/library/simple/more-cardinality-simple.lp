#program preference(more(cardinality)).
:- preference(P,more(cardinality)), optimize(P), 
   0 #sum { -1,X : holds(X),  preference(P,_,_,for(X),_); 
             1,X : holds'(X), preference(P,_,_,for(X),_)}.

