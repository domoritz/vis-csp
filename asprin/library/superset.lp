#program preference(superset).

better(P) :- preference(P,superset); required(P,better); 
                holds(X) : preference(P,_,_,for(X),_), holds'(X);
                1 #sum { 1 : holds(X), not holds'(X), preference(P,_,_,for(X),_)}.

bettereq(P) :- preference(P,superset); required(P,bettereq); 
                  holds(X) : preference(P,_,_,for(X),_), holds'(X).

required(P,bettereq) :- preference(P,superset); required(P,eq). 
required(P,worseeq)     :- preference(P,superset); required(P,eq). 
eq(P) :- preference(P,superset); required(P,eq); 
         bettereq(P); worseeq(P).

worseeq(P) :- preference(P,superset); required(P,worseeq); 
              not holds(X) : preference(P,_,_,for(X),_), not holds'(X).

worse(P) :- preference(P,superset); required(P,worse); 
            not holds(X) : preference(P,_,_,for(X),_), not holds'(X);
            1 #sum { 1 : not holds(X), holds'(X), preference(P,_,_,for(X),_)}.

required(P,bettereq) :- preference(P,superset); required(P,unc). 
required(P,worseeq)     :- preference(P,superset); required(P,unc). 
unc(P) :- preference(P,superset); required(P,unc); 
          not bettereq(P); not worseeq(P).

_error(M) :- M = @cat("superset: In preference element ",N," of preference statement ",P,", naming atom 'name(",X,")' is not allowed."), 
             preference(P,superset), 
             preference(P,(N,_),_,name(X),_).

_error(M) :- M = @cat("superset: In preference element ",N," of preference statement ",P,", weight '",W,"' appearing in weighted boolean formula '",W,"::",X,"' is not allowed."),
             preference(P,superset), 
             preference(P,(N,_),_,X,W), W != ().

_error(M) :- M = @cat("superset: In preference element ",N," of preference statement ",P,", element '",X,"' is not allowed."),
             preference(P,superset), 
             preference(P,(N,_),R,for(X),_), R != 1.


