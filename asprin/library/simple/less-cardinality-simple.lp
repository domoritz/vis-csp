#program preference(less(cardinality)).
:- preference(P,less(cardinality)), optimize(P), 
   #sum { -1,X : holds(X),  preference(P,_,_,for(X),_); 
           1,X : holds'(X), preference(P,_,_,for(X),_)} 0.

