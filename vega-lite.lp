% ====== Definitions ======

marktype(point;bar;line;area;rule;symbol;text;tick).
channel(x;y;color;size;shape;text;detail).
type(q;o;n;t).
primitive_type(string;number;boolean).

% ====== Query constraints ======

fieldtype(a,string).
fieldtype(b,number).

field(F) :- fieldtype(F,_).

% ====== Generate ======

% There has to be exactly one mark
1 { mark(M) : marktype(M) } 1.

% we can encode fields with channels
2 { encode(C,F,T) : channel(C), field(F), type(T) } 3.

% ====== Constraints ======

% number implies quant

% string implies ordinal or nominal
:- not encode(_,F,o), not encode(_,F,n), fieldtype(F,string).
:- not encode(_,F,q), fieldtype(F,number).

% cannot encode with the same channel twice
:- encode(C,F,T), encode(C,FF,TT), F != FF.
:- encode(C,F,T), encode(C,FF,TT), T != TT.

% cannot encode string as quantitative
:- encode(C,F,q), fieldtype(F, string).

% encoding number as quantitative requires binning
bin(C) :- encode(C,F,o), fieldtype(F,number).

% number is never nominal
:- encode(_,F,n), fieldtype(F,number).

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

% can only use certain channels
:- encode(C,_,T), not supported_channel(T,C).

% we have to use a preferred encoding unless the encoding is already uses
:- not encode(C,_,_), encode(CC,_,T), preferred(T,C,CC).

% some mark types require x and y channel
requires((point;tick;bar;line),(x;y)).
:- requires(M,C), mark(M), not encode(C,_,_).

% text mark requires text channel
:- mark(text), not encode(text,_,_).
% and row or column
:- mark(text), not encode(row,_,_), not encode(column,_,_).



% ====== Output ======
#show mark/1.
#show encode/3.

%% #show supported_channel/2.
