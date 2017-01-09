# Visualization constraints

Visualization constraints expressed with Answer Set Programming (ASP) [using the Potassco tools](http://potassco.sourceforge.net/).

Run it with aspirin

```sh
asprin/asprin vega-lite.lp asprin/library/*.lp
```

Semantics of preference http://www.star.dist.unige.it/~marco/Data/10constraints.pdf

Just clingo or gringo + clasp doesn't work since we use preference constraints.

```sh
gringo vega-lite.lp | clasp
```

or

```sh
clingo vega-lite.lp
```