#!/usr/bin/env python
from __future__ import print_function

import itertools
import subprocess
import os.path
import sys

import pickle
import yaml

from parser import *

CACHEFILE="runall_cache.pycache"
readCache = True
writeCache = True
debug = False

OPERDEFSFILE="operdefs.tex"
writeOperDefs = False

RESULTSTABLEFILE="resultstable.tex"

PREDS="numpreds.tex"

outputCache = {}
if readCache:
    if os.path.isfile(CACHEFILE):
        with open(CACHEFILE, 'rb') as input:
            outputCache = pickle.load(input)
if debug: print(yaml.dump(outputCache, default_flow_style=False))

APPENDIXFILE="raw.tex"

FULLRESULTS="fullresults.tex"

#datastructures=['Hashtable']
#datastructures=['Counter']
datastructures=['Memory']
#datastructures=['Counter','Accumulator','Set','HashTable','Stack']#,'Queue']
labels={'Counter':'counter',
        'Counter (lifted, auto-generated)':'counterauto',
        'Accumulator':'accumulator',
        'Set':'set',
        'HashTable':'hashtable',
	'Memory':'memory',
        'Stack':'stack'}
forceruns=[]
bestopt = '--poke'

#forceruns=['Queue']
# ,'Queue','UniqueID']

def getPrecondition(command, force):
    if (command in outputCache) and (not force):
        print("Cached: " + command)
        return outputCache[command]
    else:
        print("Running: " + command)

    p = subprocess.Popen(command.split(), stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    fullinput=""
    out, err = p.communicate(fullinput)

    if p.returncode != 0:
        print("Out:\n" + out + "\nErr:\n" + err)
        sys.exit(1)

    ret = {}
    ret["output"] = out.strip()

    for line in err.strip().split('\n'):
        print(line)
        l = line.split()
        print(l)
        ret[l[0][:-1]] = l[1]
        
    outputCache[command] = ret
    return ret

import pyparsing

operSet = set()

words=["zero", "one", "two", "three", "four",
       # "five", "six", "seven", "eight", "nine",
       # "ten", "eleven", "twelve", "thirteen", "fourteen",
       # "fifteen", "sixteen", "seventeen", "eightteen", "nineteen",
       # "twenty", "twentyone", "twentytwo", "twentythree", "twentyfour",
       "lots", "lots", "lots", "lots", "lots",
       "lots", "lots", "lots", "lots", "lots",
       "lots", "lots", "lots", "lots", "lots",
       "lots", "lots", "lots", "lots", "lots",
       "lots", "lots", "lots", "lots", "lots",
       "lots", "lots", "lots", "lots", "lots",
       "lots", "lots", "lots", "lots", "lots",
       "lots", "lots", "lots", "lots", "lots"]

maxwords = 2

operNameMap={ "=":"equal", "+":"plus","-":"minus" }

def latexifySmt2(l, checktype, compress):
    varCompress={"contents":"c"} if compress else {}
    if isinstance(l, list):
        assert(not isinstance(l[0], list))
        oper = latexifySmt2(l[0], checktype, compress)
        if oper in operNameMap:
            oper = operNameMap[oper]
        operSet.add(oper)
        args = [latexifySmt2(x, checktype, compress) if isinstance(x, list) else
                "\CCvar{"+(varCompress[x] if x in varCompress else x)+"}"
                for x in l[1:]]
        if compress:
            if(len(args)>maxwords):
                args[maxwords] = "\ldots"
                args = args[:maxwords+1]
            if oper == "and" or oper == "or": oper += words[len(args)]
            return "\CC"+oper+"{"+"}{".join(args)+"}"
        else:
            if oper == "and":
                return " $\\wedge$ ".join(args)
            elif oper == "or":
                return "["+"]\n\n $\\vee$ [".join(args)+"]"
            else:
                return "\CC"+oper+"{"+"}{".join(args)+"}"
    else:
        return l

def printRow(ds, method1, method2, sC, output, checktype, append=None):
    precondition = sC[bestopt]["output"]
    preconditionNoPoke = sC['--no-poke']["output"]
    if debug: print("printRow:", precondition)
    queriesPoke = sC['--poke']["smtqueries"]
    smttimePoke = sC['--poke']["time"]
    queriesNoPoke = sC['--no-poke']["smtqueries"]
    smttimeNoPoke = sC['--no-poke']["time"]
    if precondition == "false" or precondition == "true":
        pc = precondition
        pcNoPoke = preconditionNoPoke
        pccompress = pc
    else:
        parsed = pyparsing.OneOrMore(pyparsing.nestedExpr()).parseString(precondition).asList()[0]
        pc = latexifySmt2(parsed, checktype, compress=False)
        pccompress = latexifySmt2(parsed, checktype, compress=True)

        parsedNoPoke = pyparsing.OneOrMore(pyparsing.nestedExpr()).parseString(preconditionNoPoke).asList()[0]
        pcNoPoke = latexifySmt2(parsedNoPoke, checktype, compress=False)
        
        #pc = str(len(precondition))+" characters"
    if checktype == 'leftmover':
        method1, method2 = method2, method1
        checktype = 'rightmover'
    print("\\\\ ", file=output, end='')
    print(" & ".join(["\CCmethod{"+method1+"}",
                      "\CC"+checktype,
                      "\CCmethod{"+method2+"}",
                      "\CCqueries{"+queriesNoPoke+"} "+"(\CCtime{"+smttimeNoPoke+"})",
                      "\CCqueries{"+queriesPoke+"} "+"(\CCtime{"+smttimePoke+"})",
                      pccompress,
                      ]), file=output)

    print("\item " + "\CCmethod{"+method1+"}" + " " + "\CC"+checktype +"\\ "+ "\CCmethod{"+method2+"}"
          + "\n", file=append)
    print("\n Simple:\n\n"+pcNoPoke+"\n", file=append)
    print("\n Poke:\n\n"+pc+"\n", file=append)

def areEquivalent(cond1, cond2):
    a = cond2
    a = a.replace("x1","z1").replace("y1","x1").replace("z1","y1")
    a = a.replace("x2","z2").replace("y2","x2").replace("z2","y2")
    a = a.replace("x3","z3").replace("y3","x3").replace("z3","y3")
    print(a+'\n'+cond1+'\n'+cond2+'\n')
    if cond1 == a or cond1 == cond2:
        return True
    a = a.replace("(= (+ contents y1) contents)", "(= contents (+ contents y1))")
    if cond1 == a:
        return True
    a = a.replace("(= x1 y1)", "(= y1 x1)")
    if cond1 == a:
        return True
    return False
    
    
first = True

predsout = open(PREDS, 'wb')

with open(RESULTSTABLEFILE, 'wb') as output, open(APPENDIXFILE, 'wb') as appendix:
    # Data structures case-study.
    for ds in datastructures:
        if "auto" not in ds:
            if first:
                print(ds + ":", file=predsout)
                #print("\\\\ \hline \hline \n \CCrow{"+ds+"}\\\\", file=output)
                first = False
            else:
                print(", " + ds + ":", file=predsout)
                print(" \\vspace{1mm} \n\\\\ \CCrow{"+ds+"}", file=output)

        force = ds in forceruns
        
        print("\subsection{"+ds+"}", file=appendix)
        print("\\scriptsize", file=appendix)
        print("\\label{yml:"+labels[ds]+"}", file=appendix)
        print("\\input{listings/"+labels[ds]+".tex}", file=appendix)
        # print("\\begin{lstlisting}", file=appendix)

        ds=ds.lower()

        FILE=ds+".yml"
        (datanames, data, methods) = specToV1Format(fileToSpec(FILE))


        # print(open(FILE).read(), file=appendix)
        # print("\end{lstlisting}\n", file=appendix)

        if "auto" in FILE: continue

        print("\\begin{itemize}", file=appendix)

        minPred, minPredF, maxPred, maxPredF = 10000, 10000, 0, 0
        
        for method1,method2 in itertools.combinations_with_replacement(sorted(methods.keys()), 2):
            m1_str = "_".join(methods[method1][0])
            m2_str = "_".join(methods[method2][0])
            if m1_str == "": m1_str = "empty"
            if m2_str == "": m2_str = "empty"

            pred_file = "../predicates_empty.txt"
            # if not os.path.isfile(pred_file):
            #     pred_file = ds+"/predicates_"+ds+"_"+m2_str+"_"+m1_str+".txt"
            #     c = "./synth.py -q " + FILE + " " + method2 + " " + method1 + " " + pred_file
            #     method2, method1 = method1, method2
            #     m2_str, m1_str = m1_str, m2_str

            synthCall = {}
            for check in ['bowtie', 'leftmover', 'rightmover']:
              synthCall[check] = {}
              for poke in ['--poke', '--no-poke']:  
                if check == "leftmover":
                    c = "../src/synth.py -q " + FILE + " " + method2 + " " + method1 + " " + pred_file
                    cc = c + ' --check ' + "rightmover"
                else:
                    c = "../src/synth.py -q " + FILE + " " + method1 + " " + method2 + " " + pred_file
                    cc = c + ' --check ' + check
                cc += " " + poke
                synthCall[check][poke] = getPrecondition(cc, force)

            if areEquivalent(synthCall['leftmover'][bestopt]['output'],
                             synthCall['rightmover'][bestopt]['output']):
                #assert(synthCall['leftmover']['output'] == synthCall['bowtie']['output'])
                sC = synthCall['bowtie']
                printRow(ds, method1, method2, sC, output, 'bowtie', append=appendix)
                minPred = min(minPred, int(sC[bestopt]["predicates"]))
                maxPred = max(maxPredF, int(sC[bestopt]["predicates"]))
                minPredF = min(minPred, int(sC[bestopt]["predicatesFiltered"]))
                maxPredF = max(maxPredF, int(sC[bestopt]["predicatesFiltered"]))
            else:
                #print("Yipeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee")
                sC = synthCall['leftmover']
                printRow(ds, method1, method2, sC, output, 'leftmover', append=appendix)
                sC = synthCall['rightmover']
                printRow(ds, method1, method2, sC, output, 'rightmover', append=appendix)

                minPred = min(minPred, int(sC[bestopt]["predicates"]))
                maxPred = max(maxPredF, int(sC[bestopt]["predicates"]))
                minPredF = min(minPred, int(sC[bestopt]["predicatesFiltered"]))
                maxPredF = max(maxPredF, int(sC[bestopt]["predicatesFiltered"]))
        print(str(minPred)+"-"+str(maxPred)+" ("+str(minPredF)+"-"+str(maxPredF)+")%", file=predsout)
        print("\end{itemize}\n", file=appendix)

    # Ethereum case-study.
    print(getPrecondition("../src/synth.py -v --no-generate-predicates blockking.yml enter enter blockking_predicates.txt", False)['output'])
    print(getPrecondition("../src/synth.py -v --no-generate-predicates blockking_fixed.yml enter enter blockking_predicates.txt", False)['output'])


if writeCache:
    with open(CACHEFILE, 'wb') as output:
        pickle.dump(outputCache, output, pickle.HIGHEST_PROTOCOL)

if writeOperDefs:
    with open(OPERDEFSFILE, 'wb') as output:
        for o in operSet:
            print("\\newcommand{\CC"+o+"}{"+o+"  }", file=output)
