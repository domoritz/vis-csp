#program preference(less(cardinality)).

better(P) :- preference(P,less(cardinality)), required(P,better),
                1 #sum { -1,X : holds(X),  preference(P,_,_,for(X),_); 
                          1,X : holds'(X), preference(P,_,_,for(X),_)}.

required(P,better) :- required(P,bettereq).
required(P,eq)        :- required(P,bettereq).
bettereq(P) :- preference(P,less(cardinality)), required(P,bettereq),
                  1 #sum { 1: eq(P); 1: better(P) }.

eq(P) :- preference(P,less(cardinality)), required(P,eq),
         0 #sum { -1,X : holds(X),  preference(P,_,_,for(X),_); 
                   1,X : holds'(X), preference(P,_,_,for(X),_)}0. 

required(P,worse) :- required(P,worseeq).
required(P,eq)    :- required(P,worseeq).
worseeq(P) :- preference(P,less(cardinality)), required(P,worseeq),
              1 #sum { 1: eq(P); 1: worse(P) }.

worse(P) :- preference(P,less(cardinality)), required(P,worse),
            #sum { -1,X : holds(X),  preference(P,_,_,for(X),_); 
                    1,X : holds'(X), preference(P,_,_,for(X),_)}-1.


_error(M) :- M = @cat("less(cardinality): In preference element ",N," of preference statement ",P,", naming atom 'name(",X,")' is not allowed."), 
             preference(P,less(cardinality)), 
             preference(P,(N,_),_,name(X),_).

_error(M) :- M = @cat("less(cardinality): In preference element ",N," of preference statement ",P,", weight '",W,"' appearing in weighted boolean formula '",W,"::",X,"' is not allowed."),
             preference(P,less(cardinality)), 
             preference(P,(N,_),_,X,W), W != ().

_error(M) :- M = @cat("less(cardinality): In preference element ",N," of preference statement ",P,", element '",X,"' is not allowed."),
             preference(P,less(cardinality)), 
             preference(P,(N,_),R,for(X),_), R != 1.


