#script (python)

from gringo import *

# vars
holds, nholds, shown, base = [], [], [], []
enum, nmodels, answers, maxmodels = 0, 0, 1, 1


#
# auxiliary functions
#

def get(val, default):
    return val if val is not None else default

def getHolds():
    global holds
    return holds

def getNHolds():
    global nholds
    return nholds

def printShown():
    global enum, answers, shown, nmodels, noprint
    #print "Answer: " + str(answers)
    answers = answers + 1
    enum = enum + 1
    print "Answer: " + str(enum)
    if noprint == 0: print '%s' % ' '.join(map(str,shown))

def printShownOpt():
    global nmodels, noprint
    if noprint==-1: noprint=0; printShown(); noprint=-1
    else: printShown()
    print "OPTIMUM FOUND *"
    nmodels = nmodels + 1

def cat(*args):
    return ''.join(str(x) for x in args)

def handleError(m):
    global error
    error = 1
    for t in m:
        if t.name() == "_error" and len(t.args()) == 1:
            print str(t.args()[0])

#
# onModel and enumerate functions
#

def onModel(model):
    global holds, nholds, shown, maxmodels, step, nosyntax, mode
    # syntax errors
    if step == 1 and nosyntax == 0 and (Fun("_error",[]) in model.atoms(Model.TERMS)):
        handleError(model.atoms(Model.TERMS))
        return
    # shown atoms
    holds, shown = [], []
    for a in model.atoms(Model.SHOWN):
    	if (a.name() == "_holds_at_zero"): holds.append(a.args()[0])
        elif (a.name()[0] != "_"): shown.append(a)
    # false _holds_at_zero terms
    if maxmodels != 1 or mode == 1:
        nholds = []
        for a in model.atoms(Model.TERMS | Model.COMP):
        	if (a.name() == "_holds_at_zero"): nholds.append(a.args()[0])

def onModelMany(model):
    global shown, found, base
    shown = []
    for a in model.atoms(Model.SHOWN):
        if (a.name()[0] != "_"): shown.append(a)
    if found == 0 and len(shown) == len(base): # do not repeat model!
        for a in base:
            if a not in shown: printShownOpt(); return
        found = 1
    else: printShownOpt()


def doEnumerate(prg,step,maxmodels):
    global base, shown, nmodels, found, holds, nholds, mode
    if (maxmodels == 0): prg.conf.solve.models = 0
    else:                prg.conf.solve.models = maxmodels-nmodels+1
    found = 0; base = shown
    assumptions =                [(Fun("_holds",[x,0]),True)  for x in holds] + [(Fun("_holds",[x,0]),False) for x in nholds]
    if mode == 1: assumptions += [(Fun("_holds",[x,1]),False) for x in holds] + [(Fun("_holds",[x,1]),False) for x in nholds]
    prg.solve(assumptions,on_model=onModelMany)
    prg.conf.solve.models = 1

#
# main(prg)
#

def main(prg):

    # vars
    global found, shown, base, nosyntax, step, error, mode
    global enum, nmodels, answers, maxmodels, project, noprint
    step = 1
    unsat = 0
    startone = 1
    opt = []
    error = 0

    # options
    maxmodels   = get(prg.get_const("_asprin_n"),1)
    project     = get(prg.get_const("_asprin_project"),0)
    releaselast = get(prg.get_const("_asprin_release_last"),0)
    forgetopt   = get(prg.get_const("_asprin_no_opt_improving"),0)
    dovolatile  = get(prg.get_const("_asprin_do_external"),0)
    nosyntax    = get(prg.get_const("_asprin_no_syntax_check"),0)
    nobf        = get(prg.get_const("_asprin_no_boolean_formula"),0)
    tr          = get(prg.get_const("_asprin_tr"),"")
    steps       = get(prg.get_const("_asprin_steps"),0)
    noprint     = get(prg.get_const("_asprin_no_print"),0)
    heuristic   = get(prg.get_const("_asprin_heuristic"),0)
    mode        = get(prg.get_const("_asprin_mode"),0)

    # ground base
    if nobf != 0: prg.ground([("base",[])])
    else:         prg.ground([("base",[]),("_bf",[])])

    # heuristic
    if (heuristic != 0):
        prg.add("_show_heuristic",[],"#show _heuristic/3. #show _holds/2.")
        prg.ground([("_heuristic",[]),("_show_heuristic",[])])

    # syntax
    if nosyntax == 0:
        prg.ground([("_syntax_check",[])])
        prg.assign_external(Fun("_check",[]),True)

    # main loop
    while True:

        # add rules to improve on previous model
        if (step > startone) and (mode == 0):
            if (releaselast != 0) and (step - startone > 1): prg.release_external(Fun("_volatile",[0,step-2]))
            # ground to improve (with volatile or fact)
            if ((maxmodels != 1) or (releaselast != 0) or (dovolatile != 0)):
                prg.ground([("_doholds",[step-1]),("_preference",[0,step-1]),("_constraints",[0,step-1]),("_volatile_external",[0,step-1])])
                prg.assign_external(Fun("_volatile",[0,step-1]),True)
            else:
                prg.ground([("_doholds",[step-1]),("_preference",[0,step-1]),("_constraints",[0,step-1]),("_volatile_fact",[0,step-1])])

        # ground once mode
        if mode == 1:
            if step == 2:
                if maxmodels != 1: prg.ground([("_openholds",[step-1]),("_preference",[0,step-1]),("_constraints",[0,step-1]),("_volatile_external",[0,step-1])])
                else:              prg.ground([("_openholds",[step-1]),("_preference",[0,step-1]),("_constraints",[0,step-1]),("_volatile_fact",[0,step-1])])
            if maxmodels != 1 and step == (startone + 1): prg.assign_external(Fun("_volatile",[0,1]),True)

        # solve
        if mode == 1 and step > startone:
            ret = prg.solve([(Fun("_holds",[x,1]),True) for x in holds] + [(Fun("_holds",[x,1]),False) for x in nholds],on_model=onModel)
        else: ret = prg.solve(on_model=onModel)

        # syntax
        if error == 1: break
        if step == 1 and nosyntax == 0: prg.release_external(Fun("_check",[]))

        # set translation of extended rules
        if (step == 2) and (tr is not ""): prg.conf.asp.trans_ext = tr

        # if UNSAT
        if ret == SolveResult.UNSAT:

            # stop if program is unsat (step==1), last call was unsat (unsat==1) or we already computed maxmodels
            if (step==1):  print "UNSATISFIABLE"; break
            if (unsat==1): break
            #if noprint==999: print "\nAnswer: " + str(enum) + "\n" +
            if noprint==-1: print '%s' % ' '.join(map(str,shown))
            print ('OPTIMUM FOUND')
            nmodels += 1
            if (maxmodels == nmodels): break

            # relax conditions on previous models
            if mode == 0:
                prg.release_external(Fun("_volatile",[0,step-1]))
                if (releaselast == 0):
                    for i in range(startone,step-1): prg.release_external(Fun("_volatile",[0,i]))
            elif mode == 1: prg.assign_external(Fun("_volatile",[0,1]),False)

            # if no projection, enumerate many
            if (project == 0): doEnumerate(prg,step,maxmodels)
            if (maxmodels == nmodels): break

            # add rules to be different and not worse than optimal models
            if mode == 1 and step == 2: step = 0 # hack to avoid redefining _holds(X,1)
            if mode == 1: prg.ground([("_doholds",[step-1])])
            if forgetopt != 0:
                prg.ground([("_deletemodel",[]),("_preference", [step-1,0]),("_unsat_constraints", [step-1,0]),("_volatile_external",[step-1,0])])
                prg.assign_external(Fun("_volatile",[step-1,0]),True)
                for i in opt: prg.assign_external(Fun("_volatile",[i,0]),True)
                opt.append(step-1)
            else:
                prg.ground([("_deletemodel",[]),("_preference", [step-1,0]),("_unsat_constraints", [step-1,0]),("_volatile_fact",[step-1,0])])
            if mode == 1 and step == 0: step = 2

            startone = step + 1
            unsat = 1

        #if SAT
        else:
            printShown()
            if (unsat==1 and forgetopt != 0):
                for i in opt: prg.assign_external(Fun("_volatile",[i,0]),False)
            unsat = 0

        if steps == step: break
        step = step+1

    #while True

    if error != 1:
        print "\nModels       : " + str(nmodels)
        print "  Enumerated : " + str(enum) + "\n"

#end.

#program base.
#show _holds_at_zero(X) : _holds(X,0).

#program _doholds(m).
_holds(X,m) :- X = @getHolds().

#program _openholds(m).
{ _holds(X,m) } :- X = @getHolds().
{ _holds(X,m) } :- X = @getNHolds().

#program _volatile_fact(_m1,_m2).
_volatile(_m1,_m2).

#program _volatile_external(_m1,_m2).
#external _volatile(_m1,_m2).

#program _deletemodel.
:- _holds(X,0) : X = @getHolds();
   not _holds(X,0) : X = @getNHolds().

#program _syntax_check.

#external _check : not _nocheck.

_error(M) :- M = @cat("ERROR (asprin): Two different optimize statements: ",X1," and ",X2,"."),
  __optimize(X1), __optimize(X2), X1 < X2,
  _check.

_error(M) :- M = @cat("ERROR (asprin): Two preference statements with same id (",Id,"), and different type (",T1," and ",T2,")."),
  __preference(Id,T1), __preference(Id,T2), T1 < T2,
  _check.

_error(M) :- M = @cat("ERROR (asprin): Optimize statement for ",X," has no corresponding preference statement."),
  __optimize(X), not __preference(X,_),
  _check.

_error(M) :- M = @cat("ERROR (asprin): name(",X,") atom in preference statement ",P," has no corresponding preference statement."),
  __preference(P,_,_,name(X),_), not __preference(X,_),
  _check.

_link(P1,P2) :- __preference(P2,_,_,name(P1),_), _check.
_link(P1,P2) :- _link(P1,P3), _link(P3,P2), _check.
_error(M) :- M = @cat("ERROR (asprin): Cycle between name atoms with statement ",P,"."),
  _link(P,P),
  _check.

#show _error    : _error(X), _check.
#show _error(X) : _error(X), _check.

#program _bf.

_formula(F) :- __preference(_,_,_,for(F),_), not _nobf.
_formula(F) :- _formula(_not(F)),   not _nobf.

_formula(F) :- _formula(_and(F,G)), not _nobf.  _formula(G) :- _formula(_and(F,G)), not _nobf.
_formula(F) :- _formula(_or(F,G)),  not _nobf.  _formula(G) :- _formula(_or(F,G)),  not _nobf.

_complex(_not(F))   :- _formula(_not(F)),   not _nobf.
_complex(_and(F,G)) :- _formula(_and(F,G)), not _nobf.
_complex(_or(F,G))  :- _formula(_or(F,G)),  not _nobf.

_sat(_not(F))   :- _formula(_not(F)), not _sat(F),            not _nobf.
_sat(_and(F,G)) :- _formula(_and(F,G)), _sat(F), _sat(G),     not _nobf.
_sat(_or(F,G))  :- _formula(_or(F,G)), 1 { _sat(F); _sat(G)}, not _nobf.

_holds(F,0) :- _sat(F), __preference(_,_,_,for(F),_), _complex(F), not _nobf.

#program _heuristic.
#const _asprin_heuristic_value=1.
_heuristic(_holds(X,0),_asprin_heuristic_mode,_asprin_heuristic_value) :- __preference(P,_,_,for(X),_).

#program _nowarnings.
_nobf :- _nobf.
_check :- _check. _nocheck :- _nocheck.
__preference(A,B,C,D,E) :- __preference(A,B,C,D,E).
__preference(A,B) :- __preference(A,B).
__optimize(X) :- __optimize(X).
__better(X,Y,Z) :- __better(X,Y,Z).




