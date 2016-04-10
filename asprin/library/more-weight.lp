#program preference(more(weight)).

better(P) :- preference(P,more(weight)), required(P,better),
                #sum { -W,T : holds(X),  preference(P,_,_,for(X),(W,T)); 
                        W,T : holds'(X), preference(P,_,_,for(X),(W,T))}-1.

bettereq(P) :- preference(P,more(weight)), required(P,bettereq),
                  #sum { -W,T : holds(X),  preference(P,_,_,for(X),(W,T)); 
                          W,T : holds'(X), preference(P,_,_,for(X),(W,T))}0. 

eq(P) :- preference(P,more(weight)), required(P,eq),
         0 #sum { -W,T : holds(X),  preference(P,_,_,for(X),(W,T)); 
                   W,T : holds'(X), preference(P,_,_,for(X),(W,T))}0. 

worseeq(P) :- preference(P,more(weight)), required(P,worseeq),
              0 #sum { -W,T : holds(X),  preference(P,_,_,for(X),(W,T)); 
                        W,T : holds'(X), preference(P,_,_,for(X),(W,T))}.

worse(P) :- preference(P,more(weight)), required(P,worse),
            1 #sum { -W,T : holds(X),  preference(P,_,_,for(X),(W,T)); 
                      W,T : holds'(X), preference(P,_,_,for(X),(W,T))}.
                     
_error(M) :- M = @cat("more(weight): In preference element ",N," of preference statement ",P,", naming atom 'name(",X,")' is not allowed."), 
             preference(P,more(weight)), 
             preference(P,(N,_),_,name(X),_).

_error(M) :- M = @cat("more(weight): In preference element ",N," of preference statement ",P,", weight '",W,"' appearing in '",W,"::",X,"' should be a two terms tuple."),
             preference(P,more(weight)), 
             preference(P,(N,G),_,X,W), not ok(P,(N,G)).

ok(P,Q)   :- preference(P,more(weight)), 
             preference(P,Q,_,_,(A,B)).

_error(M) :- M = @cat("more(weight): In preference element ",N," of preference statement ",P,", element '",X,"' is not allowed."),
             preference(P,more(weight)), 
             preference(P,(N,_),R,for(X),_), R != 1.


