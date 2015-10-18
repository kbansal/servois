############################################################
# Abstract Spec (terms, predicates) -> Complete set of 
# predicates on which choose will work.
############################################################

from collections import defaultdict

def specToPredicates(spec, m1, m2):
    # assuming x1, x2.. args for m1, any y1, y2 for m2
    typeTermsMap = defaultdict(set)

    for m in spec.methods:
        for typ in m.terms:
            for term in m.terms[typ]:
                ttt = str(term)
                if "$" in str(ttt):
                    if m.name == m1:
                        typeTermsMap[typ].add(ttt.replace("$","x"))
                    if m.name == m2:
                        typeTermsMap[typ].add(ttt.replace("$","y"))
                else:
                    typeTermsMap[typ].add(ttt)

    ret = [ "("+p["name"]+" "+left+" "+right+")"
            for p in spec.spec["predicates"]
            for left in typeTermsMap[p["type"][0]]
            for right in typeTermsMap[p["type"][1]] ]

    return ret
