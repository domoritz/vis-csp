
%
% PROGRAM
%

gr(1..30).

1 { m(1) ; m(2) ; m(3) } 1.

a(1)    :- m(1).
b(1..5) :- m(1).

a(2)    :- m(2).
b(1..4) :- m(2).

a(1..3) :- m(3).
b(2..3) :- m(3). 

#show m/1. 
#show a/1. #show b/1.

{z(5)}.
#show z/1.


%
% PREFERENCE STATEMENTS
%

#optimize(p6).

#preference(p1,superset){
 a(X) : gr(X)
}.

#preference(p2,less(cardinality)){
  a(X) : gr(X)
}.

#preference(p3,lexico){
 2 :: name(p1);
 1 :: name(p2)
}.

#preference(p4,poset){
  a(X) : gr(X); 
  a(X) > a(Y) : gr(X), gr(Y), X = Y - 1
}.

#preference(p5,aso){
  a(X) > a(Y) || b(1) : gr(X), gr(Y), X = Y - 1
}.

#preference(p6,neg){
 name(p5)
}.

