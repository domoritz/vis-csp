
#program preference(aso).

required(P,better) :- optimize(P).
:- not better(P),  optimize(P).

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
better(P) :- preference(P,aso); required(P,better);
                bettereq(P,Id1) : preference(P,aso,Id1);
                better(P,Id2); preference(P,aso,Id2).

