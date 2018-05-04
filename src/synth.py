#!/usr/bin/env python

from __future__ import print_function
import subprocess, sys, argparse
import time
import os.path

## old parser
#from parse_abstract import ParseAbstract

from parser import *
from predicates import *
from lift import *

start_time = time.time()

########################################
# constants
########################################

cvc4=['/usr/local/bin/cvc4','--lang','smt2','--produce-models']
default_verbosity = 1

########################################
# Check CVC4 version
########################################
if not os.path.isfile(cvc4[0]):
    print("CVC4 not found. Currently searching for it at " + cvc4[0])
    print("Please update source if installed at a different location.")
    sys.exit(1)

########################################
# arguments
########################################

parser = argparse.ArgumentParser()

# required arguments
parser.add_argument('definition')
parser.add_argument('method1')
parser.add_argument('method2')
parser.add_argument('predicates')

# debugging levels
parser.add_argument('-v','--verbose',
    help='Be verbose',
    action="append_const",dest="verbose",const=True,default=[]
)
parser.add_argument('-q','--quiet',
    help='Be quieter',
    action="append_const",dest="quiet",const=True,default=[]
)
parser.add_argument('--check', choices=['bowtie', 'deterministic', 'complete', 'leftmover', 'rightmover'],
                    dest="check", default="bowtie")
parser.add_argument('--cvc4args',  dest="cvc4args", default="")

parser.add_argument('--poke', dest='poke', action='store_true',
                    help="Use poke heuristic (default, slower)")
parser.add_argument('--no-poke', dest='poke', action='store_false',
                    help="Use simple heuristic (faster, cruder)")
parser.add_argument('--generate-predicates', dest='generate_predicates', action='store_true',
                    help="Automatically generate predicates.")
parser.add_argument('--no-generate-predicates', dest='generate_predicates', action='store_false',
                    help="Automatically generate predicates.")
parser.set_defaults(poke=True)
parser.set_defaults(generate_predicates=True)

# parse and set options
args = parser.parse_args()    

AbstractFilename = args.definition
method1 = args.method1
method2 = args.method2
PredicatesFilename = args.predicates

verbosity = default_verbosity + len(args.verbose) - len(args.quiet)

if verbosity >= 1:
    print(" * * * " + AbstractFilename + " " + method1 + " " + method2 + " * * * ")

########################################
# statistics
########################################
stats = {}
stats["smtqueries"] = 0

########################################
# process abstract data structure definition
########################################

datanames = []
data = {}
methods = {}

abstractSpec = fileToSpec(AbstractFilename)
abstractSpec = liftSpec(abstractSpec)
abstractDefinition = specToSmtDef(abstractSpec)
(datanames, data, methods) = specToV1Format(abstractSpec)

err_state = ("err" in datanames) and (data["err"] == "Bool")

def generateBowtie(method1, method2):

    def mkVar(name, type):
        return "(declare-fun " + name + " () " + type + ')\n'
    def preArgsList(prefix, argslist):
        return ' '.join([s+prefix for s in datanames]+argslist)
    def postArgsList(oldprefix, newprefix, argslist):
        return ' '.join([s+oldprefix for s in datanames]+
                        argslist+
                        [s+newprefix for s in datanames]+
                        ["result"+newprefix])

    ret=''
    if not method1 in methods:
        print(method1, " defintion not found")
        sys.exit(2)
    if not method2 in methods:
        print(method2, " defintion not found")
        sys.exit(2)

    (m1args_type, m1result_type) = methods[method1]
    (m2args_type, m2result_type) = methods[method2]
    m1numargs = len(m1args_type)
    m2numargs = len(m2args_type)
    m1args_name = [ "x"+str(n+1) for n in range(m1numargs) ]
    m2args_name = [ "y"+str(n+1) for n in range(m2numargs) ]

    for i in range(m1numargs):
        ret+=mkVar(m1args_name[i], m1args_type[i])
    for i in range(m2numargs):
        ret+=mkVar(m2args_name[i], m2args_type[i])
    for dataname in datanames:
        for suffix in ['', '1', '2', '12', '21']:
            ret+=mkVar(dataname+suffix, data[dataname])

    ret+=mkVar("result1", m1result_type)
    ret+=mkVar("result21", m1result_type)
    ret+=mkVar("result2", m2result_type)
    ret+=mkVar("result12", m2result_type)

    ret += '(define-fun oper () Bool (and \n'
    # oper1
    ret += '  (' + method1 + '_pre_condition '+preArgsList('', m1args_name) + ')\n';
    ret += '  (' + method1 + '_post_condition '+postArgsList('', '1', m1args_name) + ')\n';
    # oper21
    ret += '  (' + method1 + '_pre_condition '+preArgsList('2', m1args_name) + ')\n';
    ret += '  (' + method1 + '_post_condition '+postArgsList('2', '21', m1args_name) + ')\n';
    # oper2
    ret += '  (' + method2 + '_pre_condition '+preArgsList('', m2args_name) + ')\n';
    ret += '  (' + method2 + '_post_condition '+postArgsList('', '2', m2args_name) + ')\n';
    # oper12
    ret += '  (' + method2 + '_pre_condition '+preArgsList('1', m2args_name) + ')\n';
    ret += '  (' + method2 + '_post_condition '+postArgsList('1', '12', m2args_name) + ')\n';
    if err_state:
        if args.check == "bowtie":
            ret += '  (or (not err12) (not err21))'
        elif args.check == "leftmover":
            ret += '  (not err21)'
        elif args.check == "rightmover":
            ret += '  (not err12)'
    ret += '))\n'

    if args.check == "deterministic":
        ret += '(define-fun deterministic () Bool (=> (and \n'
        # sigma0 ---m1--->sigma1
        ret += '  (' + method1 + '_pre_condition '+preArgsList('', m1args_name) + ')\n';
        ret += '  (' + method1 + '_post_condition '+postArgsList('', '1', m1args_name) + ')\n';
        # sigma0 ---m1--->sigma2
        ret += '  (' + method1 + '_pre_condition '+preArgsList('', m1args_name) + ')\n';
        ret += '  (' + method1 + '_post_condition '+postArgsList('', '2', m1args_name) + '))\n';
        # equal
        if err_state: ret += '  (or err1 err2 \n  '
        ret += ' (and (= result1 result2) (states_equal '+preArgsList('1',[])+' '+preArgsList('2',[])+'))\n'
        if err_state: ret += '   )\n'
        ret += '  ))\n'
    if args.check == "complete":
        ret += '(define-fun complete () Bool (=> \n'
        # sigma0 ---m1--->sigma1
        ret += '  (' + method1 + '_pre_condition '+preArgsList('', m1args_name) + ')\n';
        ret += '  (exists ('
        for dataname in datanames:
            ret+= '('+dataname+"_" + ' '+ data[dataname]+') '
        ret += '(result_ ' + m1result_type +')'
        ret += ')\n'
        ret += '    (' + method1 + '_post_condition '+postArgsList('', '_', m1args_name) + ')\n';
        ret += '  )))\n'
        # # sigma0 ---m1--->sigma2
        # ret += '  (' + method1 + '_pre_condition '+preArgsList('', m1args_name) + ')\n';
        # ret += '  (' + method1 + '_post_condition '+postArgsList('', '2', m1args_name) + '))\n';
        # # equal
        # ret += ' (and (= result1 result2) (states_equal '+preArgsList('1',[])+' '+preArgsList('2',[])+'))))\n'

    ret += '(define-fun bowtie () Bool (and \n'
    ret += '   (= result1 result21)\n'
    ret += '   (= result2 result12)\n   '
    ret += '   (states_equal '+preArgsList('12',[])+' '+preArgsList('21',[])+')\n'
    ret+= '))\n'

    return ret

bowtie = generateBowtie(method1, method2)

if verbosity >= 3:
    print(abstractDefinition)
    print(bowtie)

########################################
# process predicates
########################################

predicates = []

## load predicates from file
try:
    predicates += [line.strip() for line in open(PredicatesFilename)]
except:
    if verbosity >= 1: print("Predicates file not found, skipping.")

## autogenerated predicates
if args.generate_predicates:
    predicates += specToPredicates(abstractSpec, method1, method2)
else:
    if verbosity >= 1: print("Skipping automatic predicate generation.")

if len(predicates) == 0:
    print("ERROR: no predicates.")
    sys.exit(1)

########################################
# main
########################################

answer_complete = True
top = []
bottom = []

def nary(operator, l):
    assert(operator == 'and' or operator == 'or')
    if len(l)==0:
        return 'true' if operator == 'and' else 'false'
    elif len(l)==1:
        return l[0]
    else:
        return '('+operator+' '+' '.join(l)+')'

def current_precondition():
    #or_regions = [('(and '+' '.join(s)+')' if len(s) > 1 else s[0]) for s in top]
    or_regions = [ nary('and', s) for s in top ]
    # ret = '(or '+' '.join(or_regions)+')' if len(or_regions) > 1 else or_regions[0]
    ret = nary('or', or_regions)
    if answer_complete == False:
        print("Warning: Incomplete.")
        and_regions = [ret] + ['(not '+('(and '+' '.join(s)+')' if len(s) > 1 else s[0])+')' for s in bottom]
        ret = '(and '+' '.join(and_regions)+')'
    return ret

def top_as_formula():    return nary('or', [ nary('and', s) for s in top ] )
def bottom_as_formula(): return nary('or', [ nary('and', s) for s in bottom ] )

def query(s):
    return '(push 1)(assert (not '+s+'))(check-sat)(pop 1)\n'

def filterPredicates(predicates):
    fullinput = "(set-logic ALL_SUPPORTED)\n"
    fullinput += (abstractDefinition + bowtie)
    for p in predicates:
        fullinput += query(p)
        fullinput += query('(not '+p+')')
    stats["smtqueries"] += 1
    p = subprocess.Popen(cvc4+args.cvc4args.split()+['--incremental'],
                         stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE)
    out, err = p.communicate(fullinput)
    outlines=out.split()
    if len(outlines) != len(predicates)*2:
        print("Input:"+fullinput+"\nOut:\n" + out + "\nErr:\n" + err)
        print("Something went wrong. filterPredicates exit point A.")
        exit(1)
    return [predicates[i] for i in range(len(predicates))
            if outlines[2*i]=="sat" and outlines[2*i+1]=="sat"]
    
def simplifyUsingSMTSolver(precondition):
    fullinput = "(set-logic ALL_SUPPORTED)\n"
    fullinput += (abstractDefinition + bowtie)
    fullinput += "(assert " + precondition + ")\n"
    fullinput += "(check-sat)\n"
    p = subprocess.Popen(cvc4+args.cvc4args.split()+['--dump=assertions','--dag-thresh=0','--simplification none'],
                         stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE)
    out, err = p.communicate(fullinput)
    for l in out.splitlines():
        if len(l)>8 and l[0:8]=="(assert ":
            return l[8:-1]
    return precondition
    

def valid(formula, getvalue=[], getvalue_result={}):
    stats["smtqueries"] += 1

    fullinput = "(set-logic ALL_SUPPORTED)\n"
    fullinput += (abstractDefinition +
                  bowtie +
                  '(assert (not ' + formula + '))\n' +
                  '(check-sat)\n')

    for pred in getvalue:
        fullinput += "(get-value ("+pred+"))\n"
    
    if verbosity >= 3:
        print(";;; valid("+formula+"):")
        print(fullinput)

    p = subprocess.Popen(cvc4+args.cvc4args.split(),
                         stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE)

    out, err = p.communicate(fullinput)

    outlines = out.splitlines()
    
    # if verbosity >= 2:print("valid("+formula+"):" + out.strip())

    # print(outlines)
    
    if(len(outlines) > 0 and outlines[0] == "unsat"):
        return True
    elif(len(outlines) > 0 and outlines[0] == "sat"):
        if p.returncode != 0:
            print("Out:\n" + out + "\nErr:\n" + err)
            sys.exit(1)

        for i in range(len(outlines[1:])):
            out = outlines[1+i]
            pred = getvalue[i]
            if "false)" in out:
                getvalue_result[pred] = "false"
            elif "true)" in out:
                getvalue_result[pred] = "true"
            else:
                print("Exit at error point A in valid()")
    else:
        if p.returncode != 0:
            print("Out:\n" + out + "\nErr:\n" + err)
            sys.exit(1)
        print("Exit at error point B in valid()")
    return (out == "unsat\n")

def ret_from_1_and_2(p, ret1, ret2):
  # ret_t = nary("or", [
  #      nary("and", [predicates[i], ret_1_t])
  #      nary("and", ["(not " + predicates[i] + ")", ret_2_t])])
  #
  # Simplifications:
  # 1. If ret_1_t == ret_2_t: return ret_1_t
  # 2a. If ret_1_t == true: return (or p ret_2_t)
  # 2b. If ret_2_t == true: return (or ret_1_t (not p))
  # 3a. If ret_1_t == false: return ret_2_t
  # 3b. If ret_2_t == false: return ret_1_t
  #
  # Similarily for ret_1_f/ret_2_f.
  assert(ret1 != "true" or ret2 != "true")
  if ret1 == ret2: return ret1
  if ret1 == "true": return nary("or", [p, ret2])
  if ret2 == "true": return nary("or", [ret1, "(not " + p + ")"])
  if ret1 == "false": return nary("and", ["(not " + p + ")", ret2])
  if ret2 == "false": return nary("and", [p, ret1])
  return nary("or", [nary("and", [p, ret1]),
                     nary("and", ["(not " + p + ")", ret2])])


# When poke=False, return assumming H[1:-1] split of H[-1] that commutes,
# and that doesn't.
def synth(H, i, poke=False):
    global answer_complete

    b_query = "(=> " + nary('and', H) + " (not bowtie))"
    b_getvalue = {}
    b_result = valid(b_query, predicates[i:], b_getvalue)
    if b_result:
        if poke:
            return 0
        bottom.append(H[1:])
        return ("false", "true")

    t_query = "(=> " + nary('and', H) + " bowtie)"
    t_getvalue = {}
    t_result = valid(t_query, predicates[i:], t_getvalue)
    if t_result:
        if poke:
            return 0
        top.append(H[1:])
        return ("true", "false")

    interesting_indices = []
    for j in range(len(predicates[i:])):
        # print(p, b_getvalue[p], t_getvalue[p])
        p = predicates[i+j]
        if( b_getvalue[p] != t_getvalue[p] ):
            #print(" Yippee: ", p)
            interesting_indices.append( (1000, len(p.split(' ')), i+j) )
    if verbosity >= 2:
        print("Pre-filtering: ", len(predicates[i:]),
              ", Post-filtering: ", len(interesting_indices))

    if poke:
        return len(interesting_indices)

    interesting_indices = sorted(interesting_indices)

    if args.poke:
        #print("Poking:", end='')
        for loopvar in range(len(interesting_indices)):
            (weight, length, index) = interesting_indices[loopvar]
            w1 = synth(H + [predicates[index]], i + 1, True)
            w2 = synth(H + ["(not "+predicates[index]+")"], i + 1, True)
            #print((predicates[index],w1,w2), end='')
            interesting_indices[loopvar] = (w1+w2, length, index)
        #print('\n')
    
    interesting_indices = sorted(interesting_indices)
    #print(interesting_indices)

    if len(predicates) == i:
        print("Couldn't finish: ", H)
        answer_complete = False
        return ["false", "false"]

    if len(interesting_indices) > 0:
        j = interesting_indices[0][2]
        predicates[i], predicates[j] = predicates[j], predicates[i]
    
    (ret_1_t, ret_1_f)  = synth(H + [predicates[i]], i + 1)
    (ret_2_t, ret_2_f) = synth(H + ["(not " + predicates[i] + ")"], i + 1)
    ret_t = ret_from_1_and_2(predicates[i], ret_1_t, ret_2_t)
    ret_f = ret_from_1_and_2(predicates[i], ret_1_f, ret_2_f)
    return ret_t, ret_f
    # if ret_1_t == ret_2_t:
    #   ret_t = ret_1_t
    # else:
    # if ret_1_f == ret_2_f:
    #   ret_f = ret_1_f
    # else:
    #     return ([[predicates[i]] + l for l in ret_1]+
    #             [["(not " + predicates[i] + ")"]+l for l in ret_2])

if args.check == "deterministic":
    print(valid("deterministic"))
    exit(0)

if args.check == "complete":
    print(valid("complete"))
    exit(0)

#def trivialPredicate(predicate, m1, m2):
# for p in predicates:
#     print(p, valid(p), valid("(not "+p+")"))
if verbosity >= 2:print('\n'.join(predicates))
## this requires 2*k invokations, which can be done in...
# predicates = [ p for p in predicates if
#                not(valid(p)) and not(valid("(not "+p+")")) ]


stats["predicates"] = len(predicates)
predicates = filterPredicates(predicates)  # one call
stats["predicatesFiltered"] = len(predicates)

if verbosity >= 2:print("***")
if verbosity >= 2:print('\n'.join(predicates))

top_expr, bot_expr = synth(["oper"], 0)

if verbosity >= 2:print("top:    ", top_as_formula())
if verbosity >= 2:print("bottom: ", bottom_as_formula())
if verbosity >= 2:print("top_expr:", simplifyUsingSMTSolver(top_expr))
if verbosity >= 2:print("bot_expr:", simplifyUsingSMTSolver(bot_expr))


if verbosity >= 2:
    print("Completeness check: ", end='')
    valid( "(or (not oper) " + top_as_formula() + " " + bottom_as_formula() + ")" )
    print("Soundness check: ", end='')
    valid( "(not (and oper " + top_as_formula() + " " + bottom_as_formula() + "))" )

answer=current_precondition()
answer=simplifyUsingSMTSolver(answer)

print(answer)

end_time = time.time()
stats["time"] = ("%.2f" % (end_time - start_time))

for stat in stats:
    print(stat + ",", stats[stat], file=sys.stderr)
