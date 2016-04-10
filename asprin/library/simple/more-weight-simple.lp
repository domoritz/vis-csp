#program preference(more(weight)).
:- preference(P,more(weight)), optimize(P),
   0 #sum { -W,T : holds(X),  preference(P,_,_,for(X),(W,T)); 
             W,T : holds'(X), preference(P,_,_,for(X),(W,T))}.
