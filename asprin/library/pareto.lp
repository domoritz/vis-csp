#program preference(pareto).

required(Q,better)   :- preference(P,pareto), required(P,better), preference(P,_,_,name(Q),_).
required(Q,bettereq) :- preference(P,pareto), required(P,better), preference(P,_,_,name(Q),_).
better(P) :- preference(P,pareto), required(P,better),
	            bettereq(Q) : preference(P,_,_,name(Q),_);
                better(R);    preference(P,_,_,name(R),_).

required(Q,bettereq) :- preference(P,pareto), required(P,bettereq), preference(P,_,_,name(Q),_).
bettereq(P) :- preference(P,pareto), required(P,bettereq),
	              bettereq(Q) : preference(P,_,_,name(Q),_).

required(Q,eq) :- preference(P,pareto), required(P,eq), preference(P,_,_,name(Q),_).
eq(P) :- preference(P,pareto), required(P,eq),
	     eq(Q) : preference(P,_,_,name(Q),_).

required(Q,worseeq) :- preference(P,pareto), required(P,worseeq), preference(P,_,_,name(Q),_).
worseeq(P) :- preference(P,pareto), required(P,worseeq),
	          worseeq(Q) : preference(P,_,_,name(Q),_).

required(Q,worse)   :- preference(P,pareto), required(P,worse), preference(P,_,_,name(Q),_).
required(Q,worseeq) :- preference(P,pareto), required(P,worse), preference(P,_,_,name(Q),_).
worse(P) :- preference(P,pareto), required(P,worse),
	        worseeq(Q) : preference(P,_,_,name(Q),_);
            worse(R);    preference(P,_,_,name(R),_).

required(P,bettereq) :- preference(P,pareto), required(P,unc). 
required(P,worseeq)     :- preference(P,pareto), required(P,unc). 
unc(P) :- preference(P,pareto); required(P,unc); 
          not bettereq(P); not worseeq(P).

%%% no formulas
_error(M) :- M = @cat("pareto: In preference element ",N," of preference statement ",P,", only naming atoms are allowed."), 
             preference(P,pareto), 
             preference(P,(N,_),_,for(X),_).

%%% no weights
_error(M) :- M = @cat("pareto: In preference element ",N," of preference statement ",P,", weight '",W,"' appearing in '",W,"::",X,"' is not allowed."),
             preference(P,pareto), 
             preference(P,(N,_),_,X,W), W != ().

%%% no orders or conditions
_error(M) :- M = @cat("pareto: In preference element ",N," of preference statement ",P,", element '",X,"' is not allowed."),
             preference(P,pareto), 
             preference(P,(N,_),R,for(X),_), R != 1.

