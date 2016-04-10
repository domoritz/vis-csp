#program preference(subset).

better(P) :- preference(P,subset); required(P,better); 
                not holds(X) : preference(P,_,_,for(X),_), not holds'(X);
                1 #sum { 1 : not holds(X), holds'(X), preference(P,_,_,for(X),_)}.

bettereq(P) :- preference(P,subset); required(P,bettereq); 
                  not holds(X) : preference(P,_,_,for(X),_), not holds'(X).

required(P,bettereq) :- preference(P,subset); required(P,eq). 
required(P,worseeq)     :- preference(P,subset); required(P,eq). 
eq(P) :- preference(P,subset); required(P,eq); 
         bettereq(P); worseeq(P).

worseeq(P) :- preference(P,subset); required(P,worseeq); 
              holds(X) : preference(P,_,_,for(X),_), holds'(X).

worse(P) :- preference(P,subset); required(P,worse); 
            holds(X) : preference(P,_,_,for(X),_), holds'(X);
            1 #sum { 1 : holds(X), not holds'(X), preference(P,_,_,for(X),_)}.

required(P,bettereq) :- preference(P,subset); required(P,unc). 
required(P,worseeq)     :- preference(P,subset); required(P,unc). 
unc(P) :- preference(P,subset); required(P,unc); 
          not bettereq(P); not worseeq(P).

_error(M) :- M = @cat("subset: In preference element ",N," of preference statement ",P,", naming atom 'name(",X,")' is not allowed."), 
             preference(P,subset), 
             preference(P,(N,_),_,name(X),_).

_error(M) :- M = @cat("subset: In preference element ",N," of preference statement ",P,", weight '",W,"' appearing in weighted boolean formula '",W,"::",X,"' is not allowed."),
             preference(P,subset), 
             preference(P,(N,_),_,X,W), W != ().

_error(M) :- M = @cat("subset: In preference element ",N," of preference statement ",P,", element '",X,"' is not allowed."),
             preference(P,subset), 
             preference(P,(N,_),R,for(X),_), R != 1.




