#program preference(lexico).

required(Q,better) :- preference(P,lexico), required(P,better), preference(P,_,_,name(Q),_).
required(Q,eq)        :- preference(P,lexico), required(P,better), preference(P,_,_,name(Q),_).
better(P) :- preference(P,lexico), required(P,better),
                better(R); preference(P,_,_,name(R),(L));
	            eq(Q)      : preference(P,_,_,name(Q),(LL)), LL > L.

required(P,better) :- preference(P,lexico), required(P,bettereq). 
required(P,eq)        :- preference(P,lexico), required(P,bettereq). 
bettereq(P) :- preference(P,lexico), required(P,bettereq),
                  1 #sum { 1: better(P); 1: eq(P) }.

required(Q,eq) :- preference(P,lexico), required(P,eq), preference(P,_,_,name(Q),_).
eq(P) :- preference(P,lexico), required(P,eq),
         eq(Q) : preference(P,_,_,name(Q),_).

required(P,worse) :- preference(P,lexico), required(P,worseeq). 
required(P,eq)    :- preference(P,lexico), required(P,worseeq). 
worseeq(P) :- preference(P,lexico), required(P,worseeq),
              1 #sum { 1: worse(P); 1: eq(P) }.

required(Q,worse) :- preference(P,lexico), required(P,worse), preference(P,_,_,name(Q),_).
required(Q,eq)    :- preference(P,lexico), required(P,worse), preference(P,_,_,name(Q),_).
worse(P) :- preference(P,lexico), required(P,worse),
            worse(R); preference(P,_,_,name(R),(L));
	        eq(Q) : preference(P,_,_,name(Q),(LL)), LL > L.

required(P,bettereq) :- preference(P,lexico), required(P,unc). 
required(P,worseeq)     :- preference(P,lexico), required(P,unc). 
unc(P) :- preference(P,lexico); required(P,unc); 
          not bettereq(P); not worseeq(P).

%%% no formulas
_error(M) :- M = @cat("lexico: In preference element ",N," of preference statement ",P,", only naming atoms are allowed."), 
             preference(P,lexico), 
             preference(P,(N,_),_,for(X),_).

%%% weights allowed

%%% no orders or conditions
_error(M) :- M = @cat("lexico: In preference element ",N," of preference statement ",P,", element '",X,"' is not allowed."),
             preference(P,lexico), 
             preference(P,(N,_),R,for(X),_), R != 1.

