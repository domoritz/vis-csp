% ====== Definitions ======

marktype(point;bar;line;area;rule;symbol;text;tick).
channel(x;y;color;size;shape;text;detail).
type(q;o;n).
primitive_type(string;number;boolean).
agg_func(count;mean;median;min;max).

% ====== Data definitions ======

fieldtype(s1,string).
fieldtype(s2,string).

fieldtype(n1,number).
fieldtype(n2,number).

field(F) :- fieldtype(F,_).

% ====== Generate ======

% There has to be exactly one mark
{ mark(M) : marktype(M) } = 1.

% we can encode fields with channels
{ encode(C,F,T) : channel(C), field(F), type(T) } = 2.

0 { aggregate(C,F): agg_func(F) } 1 :- encode(C,_,_).

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
:- encode(C,F,_), encode(C,FF,_), F != FF.
:- encode(C,_,T), encode(C,_,TT), T != TT.

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

% supported encoding channels
:- mark(point), encode(text,_,_).
:- mark(tick;bar), encode((shape;size;detail;text),_,_).
:- mark(line;area), encode((shape;size;text),_,_).
:- mark(text), encode((x;y;shape;size;detail),_,_).

% cannot bin and aggregate
:- bin(C), aggregate(C,_).

% orientation for bars and ticks
orientation(horizontal) :- mark(bar;tick), encode(x,_,(o;n)).
orientation(vertical) :- mark(bar;tick), encode(y,_,(o;n)).

% ====== Preferences ======

% encoding channel preferences
preferred_channel(q,(x;y),size).
preferred_channel(q,size,color).
preferred_channel(q,color,text).
preferred_channel((o;n),(x;y),(column;row)).
preferred_channel((o;n),(column;row),color).
preferred_channel(o,color,size).
preferred_channel(n,color,shape).

% transitivity of preferences
preferred_channel(T,C,CCC) :- preferred_channel(T,C,CC), preferred_channel(T,CC,CCC).

supported_channel(T,C) :- preferred_channel(T,C,_).
supported_channel(T,C) :- preferred_channel(T,_,C).

% can only use supported channels
:- encode(C,_,T), not supported_channel(T,C).

% prefer certain encoding channel (depend on type)
#preference(pencoding,poset){
  encode(C,F,T) > encode(CC,F,T) : preferred_channel(T,C,CC), field(F)
}.

% prefer quantitative > ordinal > nominal
#preference(ptype,poset){
  encode(C,F,q) > encode(C,F,o) : channel(C), field(F);
  encode(C,F,o) > encode(C,F,n) : channel(C), field(F)
}.

is_q :- encode(x,_,q), not encode(y,_,_).
is_q :- encode(y,_,q), not encode(x,_,_).

is_o_o_or_n_n :- encode(x,_,o), encode(y,_,o).
is_o_o_or_n_n :- encode(x,_,n), encode(y,_,n).

is_q_n :- encode(x,_,q), encode(y,_,n).
is_q_n :- encode(y,_,q), encode(x,_,n).

is_q_o :- encode(x,_,q), encode(y,_,o).
is_q_o :- encode(y,_,q), encode(x,_,o).

is_q_q :- encode(y,_,q), encode(x,_,q).

#preference(pmark,aso){
  mark(tick) > mark(point) || is_q;
  mark(point) > mark(text) || is_q;

  mark(point) > mark(text) || is_o_o_or_n_n;

  mark(bar) > mark(point) || is_q_n;
  mark(point) > mark(text) || is_q_n;

  mark(line) > mark(bar) || is_q_o;
  mark(bar) > mark(point) || is_q_o;
  mark(point) > mark(text) || is_q_o;

  mark(point) > mark(text) || is_q_q
}.

% only use supported mark types
:- is_q, not mark(tick), not mark(point), not mark(text).
:- is_o_o_or_n_n, not mark(point), not mark(text).
:- is_q_n, not mark(bar), not mark(point), not mark(text).
:- is_q_o, not mark(line), not mark(bar), not mark(point), not mark(text).
:- is_q_q, not mark(point), not mark(text).

% minimize aggregations
#preference(pagg,less(cardinality)){
  aggregate(C,F) : agg_func(F), channel(C)
}.

% ====== Optimize preferences ======

#preference(prefs,lexico){
  1 :: name(pencoding);
  1 :: name(pmark);
  1 :: name(ptype);
  1 :: name(pagg)
}.

% throws warnings if we use this instead of the rule above
%% #preference(prefs,pareto){
%%   name(pencoding);
%%   name(pmark);
%%   name(ptype)
%% }.

#optimize(prefs).

% ====== Output ======
#show mark/1.
#show encode/3.
#show bin/1.
#show orientation/1.
#show aggregate/2.
