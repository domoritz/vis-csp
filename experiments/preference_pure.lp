dom(1..30).

3 {a(X): dom(X)} 5.

pref(X,Y):- X<Y, dom(X), dom(Y).

invalid(2).

% cannot use invalid
:- invalid(X), a(X).

% have to use preferred
:- a(Y), not a(X), not invalid(X), pref(X,Y).

#show a/1.
