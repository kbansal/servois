#!/usr/bin/env python

from __future__ import print_function
import yaml
import sys

############################################################
# Data Structures
############################################################

class State:
    """Abstract state"""
    def __init__(self, names, types):
        state.names=names
        state.types=types

class Method:
    """A method is relation between pre-state, post-state and
    arguments (args), emitting return values (rets)."""
    def __init__(self, name, args, rets, requires, ensures, terms):
        self.name = name
        self.args = args
        self.rets = rets
        self.requires = requires
        self.ensures = ensures
        self.terms = terms

class Specification:
    """Internal representation of the specification. This currently
    carries more information than just the transition relation.
    Serves as sort of intermediate format between different stages of
    the program. As the program grows this might become an issue,
    would be addressed then."""
    def __init__(self, spec):
        self.spec = spec
        self.name = spec["name"]
        self.state = spec["state"]
        self.methods = [ Method(m["name"],
                                m["args"],
                                m["return"],
                                m["requires"],
                                m["ensures"],
                                m["terms"])
                         for m in spec["methods"] ]
    def getPreamble(self):
        if "preamble" in self.spec:
            return self.spec['preamble']
        else:
            return None
    def getState(self):
        return self.spec["state"]
    def getStateNames(self):
        return [d["name"] for d in self.spec["state"]]
    def getStateTypes(self):
        data = {}
        for d in self.spec["state"]:
            data[d["name"]] = d["type"]
        return data
    def getMethods(self):
        return self.spec["methods"]
    def getStatesEqualDefinition(self):
        if "states_equal" in self.spec:
            return self.spec["states_equal"]["definition"]
        # compute the definition automatically as just equality
        return And(["(= %s_1 %s_2)" % (s,s) for s in self.getStateNames()])
    def getPredicates(self):
        return self.spec["predicates"]



############################################################
# SMT
############################################################

def DeclareFun(name, args, return_type):
    ret = ""
    ret += "(declare-fun " + name + "\n"
    ret += "  ( "
    ret += '\n    '.join(["("+arg["name"] + " " + arg["type"]+")" for arg in args])
    ret += " )\n"
    ret += "  " + return_type + "\n"
    ret += " )\n"
    return ret

def DefineFun(name, args, return_type, definition):
    ret = ""
    ret += "(define-fun " + name + "\n"
    ret += "  ( "
    ret += '\n    '.join(["("+arg["name"] + " " + arg["type"]+")" for arg in args])
    ret += " )\n"
    ret += "  " + return_type + "\n"
    ret += "  " + definition.strip().replace("\n","\n  ") + "\n"
    ret += " )\n"
    return ret

def And(l):
    if not l: return "true"
    if len(l) == 1: return l[0]
    return "(and " + " ".join(l) + ")"

############################################################
# Abstract Spec -> Abstract SMT Definition
############################################################

def specToSmtDef(spec):
    ret = ""
    ret += ";; BEGIN: specToSmtDef( " + spec.name + " )"
    ret += "\n\n"

    if spec.getPreamble():
        ret += spec.getPreamble()
        ret += "\n"

    s1 = StateVar(spec.getState(), "_1")
    s2 = StateVar(spec.getState(), "_2")

    ret += DefineFun("states_equal", s1+s2, "Bool",
                     spec.getStatesEqualDefinition())
    ret += "\n"

    for m in spec.getMethods():
        s = StateVar(spec.getState(), "")

        sOld = StateVar(spec.getState(), "")
        sNew = StateVar(spec.getState(), "_new")

        name = m["name"] + "_pre_condition"
        args = s + m["args"]
        ret += DefineFun(name, args, "Bool", m["requires"])
        ret += "\n"

        name = m["name"] + "_post_condition"
        args = sOld + m["args"] + sNew + m["return"]
        ret += DefineFun(name, args, "Bool", m["ensures"])
        ret += "\n"

    ret += ";; END: specToSmtDef( " + spec.name + " )\n"

    return ret

############################################################
# Util
############################################################

def fileToSpec(file):
    """Take specification specified in a YML file, and convert to
    internal data structures."""

    stream = open(file, 'r') if file is not None else sys.stdin
    return Specification(yaml.load(stream))

def StateVar(s, varname):
    return [{'name': x['name'] + varname, 'type':x['type']} 
            for x in s]


############################################################
# For combatibility with old version of synth
############################################################

def specToV1Format(spec):
    """Convert specification for combatability with the old
    version. Serves as drop-in replacement of ParseAbstract
    function."""

    ## State processing
    datanames = spec.getStateNames()
    data = spec.getStateTypes()

    ## Methods process 
    methods = {}
    for m in spec.getMethods():
        methods[m["name"]] = ([a["type"] for a in m["args"]],
                              m["return"][0]['type'])
    return (datanames, data, methods)
