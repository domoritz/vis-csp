#program preference(and).

required(Q,better) :- preference(P,and), required(P,better), preference(P,_,_,name(Q),_).
better(P) :- preference(P,and), required(P,better); 
	            better(Q) : preference(P,_,_,name(Q),_).
            
required(P,better) :- preference(P,and), required(P,bettereq). 
required(P,eq)        :- preference(P,and), required(P,bettereq). 
bettereq(P) :- preference(P,and), required(P,bettereq),
                  1 #sum { 1: better(P); 1: eq(P) }.

required(Q,eq) :- preference(P,and), required(P,eq), preference(P,_,_,name(Q),_).
eq(P) :- preference(P,and), required(P,eq); 
	     eq(Q) : preference(P,_,_,name(Q),_).

required(P,worse) :- preference(P,and), required(P,worseeq). 
required(P,eq)    :- preference(P,and), required(P,worseeq). 
worseeq(P) :- preference(P,and), required(P,worseeq),
              1 #sum { 1: worse(P); 1: eq(P) }.

required(Q,worse) :- preference(P,and), required(P,worse), preference(P,_,_,name(Q),_).
worse(P) :- preference(P,and), required(P,worse); 
	        worse(Q) : preference(P,_,_,name(Q),_).

required(P,bettereq) :- preference(P,and), required(P,unc). 
required(P,worseeq)     :- preference(P,and), required(P,unc). 
unc(P) :- preference(P,and); required(P,unc); 
          not bettereq(P); not worseeq(P).

%%% no formulas
_error(M) :- M = @cat("and: In preference element ",N," of preference statement ",P,", only naming atoms are allowed."), 
             preference(P,and), 
             preference(P,(N,_),_,for(X),_).

%%% no weights
_error(M) :- M = @cat("and: In preference element ",N," of preference statement ",P,", weight '",W,"' appearing in '",W,"::",X,"' is not allowed."),
             preference(P,and), 
             preference(P,(N,_),_,X,W), W != ().

%%% no orders or conditions
_error(M) :- M = @cat("and: In preference element ",N," of preference statement ",P,", element '",X,"' is not allowed."),
             preference(P,and), 
             preference(P,(N,_),R,for(X),_), R != 1.

