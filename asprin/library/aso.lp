
#program preference(aso).

required(P,aso) :- preference(P,aso), required(P,_).
preference(P,aso,Id) :- preference(P,aso), required(P,aso), preference(P,Id,_,_,_).

nohead(P,Id) :- preference(P,aso,Id), 
                not holds(X) : preference(P,Id,H,for(X),_), H!=0.

nohead'(P,Id) :- preference(P,aso,Id), 
                 not holds'(X) : preference(P,Id,H,for(X),_), H!=0.

value'(P,Id,V) :- preference(P,aso,Id),
                  V = #min { 1   : not holds'(X), preference(P,Id,0,for(X),_);
                             1   : nohead'(P,Id);
                             Pos : holds'(X), preference(P,Id,Pos,for(X),_), Pos != 0}.
 
better(P,Id) :- preference(P,aso,Id), value'(P,Id,V), required(P,aso,better), 
                   V > #min { 1   : not holds(X), preference(P,Id,0,for(X),_);
                              1   : nohead(P,Id);
                              Pos : holds(X), preference(P,Id,Pos,for(X),_), Pos != 0}.
 
bettereq(P,Id) :- preference(P,aso,Id), value'(P,Id,V), required(P,aso,bettereq),
                     V >= #min { 1   : not holds(X), preference(P,Id,0,for(X),_);
                                 1   : nohead(P,Id);
                                 Pos : holds(X), preference(P,Id,Pos,for(X),_), Pos != 0}.

required(P,aso,better)   :- preference(P,aso), required(P,better).                             
required(P,aso,bettereq) :- preference(P,aso), required(P,better).                             
better(P) :- preference(P,aso), required(P,better),
                bettereq(P,Id1) : preference(P,aso,Id1);
                better(P,Id2), preference(P,aso,Id2).

required(P,aso,bettereq) :- preference(P,aso), required(P,bettereq).                            
bettereq(P) :- preference(P,aso), required(P,bettereq),
                  bettereq(P,Id) : preference(P,aso,Id).

              
eq(P,Id) :- preference(P,aso,Id), value'(P,Id,V), required(P,aso,eq),
            V = #min { 1   : not holds(X), preference(P,Id,0,for(X),_);
                       1   : nohead(P,Id);
                       Pos : holds(X), preference(P,Id,Pos,for(X),_), Pos != 0}.
 
worseeq(P,Id) :- preference(P,aso,Id), value'(P,Id,V), required(P,aso,worseeq),
                 V <= #min { 1   : not holds(X), preference(P,Id,0,for(X),_);
                             1   : nohead(P,Id);
                             Pos : holds(X), preference(P,Id,Pos,for(X),_), Pos != 0}.
 
worse(P,Id) :- preference(P,aso,Id), value'(P,Id,V), required(P,aso,worse),
               V < #min { 1   : not holds(X), preference(P,Id,0,for(X),_);
                          1   : nohead(P,Id);
                          Pos : holds(X), preference(P,Id,Pos,for(X),_), Pos != 0}.

required(P,aso,eq) :- preference(P,aso), required(P,eq).                             
eq(P) :- preference(P,aso), required(P,eq),
         eq(P,Id) : preference(P,aso,Id).

required(P,aso,worseeq) :- preference(P,aso), required(P,worseeq).                             
worseeq(P) :- preference(P,aso), required(P,worseeq),
              worseeq(P,Id) : preference(P,aso,Id).

required(P,aso,worseeq) :- preference(P,aso), required(P,worse).                             
required(P,aso,worse)   :- preference(P,aso), required(P,worse).                             
worse(P) :- preference(P,aso), required(P,worse),
            worseeq(P,Id1) : preference(P,aso,Id1);
            worse(P,Id2); preference(P,aso,Id2).

required(P,bettereq) :- preference(P,aso), required(P,unc). 
required(P,worseeq)     :- preference(P,aso), required(P,unc). 
unc(P) :- preference(P,aso); required(P,unc); 
          not bettereq(P); not worseeq(P).


_error(M) :- M = @cat("aso: In preference element ",N," of preference statement ",P,", naming atom 'name(",X,")' is not allowed."), 
             preference(P,aso), 
             preference(P,(N,_),_,name(X),_).

_error(M) :- M = @cat("aso: In preference element ",N," of preference statement ",P,", weight '",W,"' appearing in weighted boolean formula '",W,"::",X,"' is not allowed."),
             preference(P,aso), 
             preference(P,(N,_),_,X,W), W != ().


