#program preference(less(weight)).

better(P) :- preference(P,less(weight)), required(P,better),
                1 #sum { -W,T : holds(X),  preference(P,_,_,for(X),(W,T)); 
                          W,T : holds'(X), preference(P,_,_,for(X),(W,T))}.

bettereq(P) :- preference(P,less(weight)), required(P,bettereq),
                  0 #sum { -W,T : holds(X),  preference(P,_,_,for(X),(W,T)); 
                            W,T : holds'(X), preference(P,_,_,for(X),(W,T))}. 

eq(P) :- preference(P,less(weight)), required(P,eq),
         0 #sum { -W,T : holds(X),  preference(P,_,_,for(X),(W,T)); 
                   W,T : holds'(X), preference(P,_,_,for(X),(W,T))}0. 

worseeq(P) :- preference(P,less(weight)), required(P,worseeq),
              #sum { -W,T : holds(X),  preference(P,_,_,for(X),(W,T)); 
                      W,T : holds'(X), preference(P,_,_,for(X),(W,T))}0.

worse(P) :- preference(P,less(weight)), required(P,worse),
            #sum { -W,T : holds(X),  preference(P,_,_,for(X),(W,T)); 
                    W,T : holds'(X), preference(P,_,_,for(X),(W,T))}-1.

_error(M) :- M = @cat("less(weight): In preference element ",N," of preference statement ",P,", naming atom 'name(",X,")' is not allowed."), 
             preference(P,less(weight)), 
             preference(P,(N,_),_,name(X),_).

_error(M) :- M = @cat("less(weight): In preference element ",N," of preference statement ",P,", weight '",W,"' appearing in '",W,"::",X,"' should be a two terms tuple."),
             preference(P,less(weight)), 
             preference(P,(N,G),_,X,W), not ok(P,(N,G)).

ok(P,Q)   :- preference(P,less(weight)), 
             preference(P,Q,_,_,(A,B)).

_error(M) :- M = @cat("less(weight): In preference element ",N," of preference statement ",P,", element '",X,"' is not allowed."),
             preference(P,less(weight)), 
             preference(P,(N,_),R,for(X),_), R != 1.


