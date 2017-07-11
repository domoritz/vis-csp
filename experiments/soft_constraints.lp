dom(1..30).

3 {a(X): dom(X)} 5.

:- a(2).

penalty("prefer smaller", a(X), X) :- a(X).

#minimize { P: penalty(_,_,P) }.

#show a/1.
