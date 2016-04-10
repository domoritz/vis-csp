#program preference(more(cardinality)).

better(P) :- preference(P,more(cardinality)), required(P,better),
                #sum { -1,X : holds(X),  preference(P,_,_,for(X),_); 
                        1,X : holds'(X), preference(P,_,_,for(X),_)}-1.

required(P,better) :- required(P,bettereq).
required(P,eq)        :- required(P,bettereq).
bettereq(P) :- preference(P,more(cardinality)), required(P,bettereq),
                  1 #sum { 1: eq(P); 1: better(P) }.

eq(P) :- preference(P,more(cardinality)), required(P,eq),
         0 #sum { -1,X : holds(X),  preference(P,_,_,for(X),_); 
                   1,X : holds'(X), preference(P,_,_,for(X),_)}0. 

required(P,worse) :- required(P,worseeq).
required(P,eq)    :- required(P,worseeq).
worseeq(P) :- preference(P,more(cardinality)), required(P,worseeq),
              1 #sum { 1: eq(P); 1: worse(P) }.

worse(P) :- preference(P,more(cardinality)), required(P,worse),
            1 #sum { -1,X : holds(X),  preference(P,_,_,for(X),_); 
                      1,X : holds'(X), preference(P,_,_,for(X),_)}.


_error(M) :- M = @cat("more(cardinality): In preference element ",N," of preference statement ",P,", naming atom 'name(",X,")' is not allowed."), 
             preference(P,more(cardinality)), 
             preference(P,(N,_),_,name(X),_).

_error(M) :- M = @cat("more(cardinality): In preference element ",N," of preference statement ",P,", weight '",W,"' appearing in weighted boolean formula '",W,"::",X,"' is not allowed."),
             preference(P,more(cardinality)), 
             preference(P,(N,_),_,X,W), W != ().

_error(M) :- M = @cat("more(cardinality): In preference element ",N," of preference statement ",P,", element '",X,"' is not allowed."),
             preference(P,more(cardinality)), 
             preference(P,(N,_),R,for(X),_), R != 1.


