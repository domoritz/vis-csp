dom(1..8).

3 {a(X): dom(X)} 5.

:- a(2).

pref(X,Y):- X<Y, dom(X), dom(Y).

#preference(p1,poset){
  a(X) > a(Y) : pref(X,Y)
}.

#optimize(p1).

#show a/1.
