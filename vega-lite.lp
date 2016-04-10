% ====== Definitions ======

marktype(point;bar;line;area;rule;symbol;text;tick).
channel(x;y;color;size;shape;text;detail).
type(q;o;n).
primitive_type(string;number;boolean).

% ====== Data definitions ======

fieldtype(s1,string).
fieldtype(s2,string).

fieldtype(n1,number).
fieldtype(n2,number).

field(F) :- fieldtype(F,_).

% ====== Generate ======

% There has to be exactly one mark
1 { mark(M) : marktype(M) } 1.

% we can encode fields with channels
{ encode(C,F,T) : channel(C), field(F), type(T) } = 2.

% ====== Query constraints ======

% use certain mark
:- not mark(bar).

% want to use number as ordinal
%% :- not encode(_,n1,o).

:- not encode(_,n1,_).
:- not encode(_,n2,_).

% ====== Constraints ======

% cannot use string for quantitative
:- encode(_,F,q), fieldtype(F,string).

% cannot encode with the same channel twice
:- encode(C,F,T), encode(C,FF,TT), F != FF.
:- encode(C,F,T), encode(C,FF,TT), T != TT.

% cannot encode string as quantitative
:- encode(C,F,q), fieldtype(F, string).

% encoding number as ordinal or nominal requires binning
bin(C) :- encode(C,F,o), fieldtype(F,number).
bin(C) :- encode(C,F,n), fieldtype(F,number).

% text mark requires text channel
:- mark(text), not encode(text,_,_).
% and row or column
:- mark(text), not encode(row,_,_), not encode(column,_,_).

% point, tick, and bar require x or y channel
:- mark(point;tick;bar), not encode(x,_,_), not encode(y,_,_).

% line and area require x and y channel
:- mark(line;area), not encode(x,_,_).
:- mark(line;area), not encode(y,_,_).

% bar and tick requires quantitative (x or y)
:- mark(bar;tick), not encode(x,_,q), not encode(y,_,q).
% and optional ordinal/nominal (x or y); not two quantitative
:- mark(bar;tick), encode(x,_,q), encode(y,_,q).

% ====== Preferences ======

% encoding channel preferences
preferred(q,(x;y),size).
preferred(q,size,color).
preferred(q,color,text).
preferred((o;n),(x;y),(column;row)).
preferred((o;n),(column;row),color).
preferred(o,color,size).
preferred(n,color,shape).

% transitivity of preferences
preferred(T,C,CCC) :- preferred(T,C,CC), preferred(T,CC,CCC).

supported_channel(T,C) :- preferred(T,C,_).
supported_channel(T,C) :- preferred(T,_,C).

% can only use supported channels
:- encode(C,_,T), not supported_channel(T,C).

% prefer certain encoding channel (depend on type)
#preference(pencoding,poset){
  encode(C,F,T) > encode(CC,F,T) : preferred(T,C,CC), field(F)
}.

% prefer ordinal over nominal
#preference(p2,poset){
  mark(point) > mark(bar)
  %encode(C,F,o) > encode(C,F,n) : channel(C), field(F)
}.

#preference(p1,pareto){
  name(pencoding);
  name(p2)
}.

% ====== Optimize ======
#optimize(p1).

% ====== Output ======
#show mark/1.
#show encode/3.
#show bin/1.
