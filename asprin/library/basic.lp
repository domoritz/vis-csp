#program preference.
required(P,better) :- optimize(P).
:- not better(P),  optimize(P).
required(A,B) :- required(A,B). % to avoid warnings

