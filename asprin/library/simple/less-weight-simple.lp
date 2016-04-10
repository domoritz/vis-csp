#program preference(less(weight)).
:- preference(P,less(weight)), optimize(P),
   #sum { -W,T : holds(X),  preference(P,_,_,for(X),(W,T)); 
           W,T : holds'(X), preference(P,_,_,for(X),(W,T))} 0.
