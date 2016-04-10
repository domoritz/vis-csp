dom(1..8).

3 {a(X): dom(X)} 5.

:- a(2).

%% #preference(p1,aso){
%% 	a(1) > a(2);
%% 	a(2) > a(3);
%% 	a(3) > a(4);
%% 	a(4) > a(5);
%% 	a(5) > a(6);
%% 	a(6) > a(7);
%% 	a(7) > a(8)
%% }.

pref(X,Y):- X<Y, dom(X), dom(Y).

#preference(p1,poset){
  a(X) > a(Y) : pref(X,Y)
}.

%% #preference(p1,poset){
%%   a(X) : dom(X);
%%   a(X) > a(Y) : pref(X,Y)
%% }.


#optimize(p1).

#show a/1.
