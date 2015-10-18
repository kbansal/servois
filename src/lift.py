# Takes as input a YML specification of the data structures, and
# outputs a new one where each method action is "total" by
# introducing an "err" state.

from parser import *

def liftSpec(old_spec):
    spec = old_spec.spec
    for s in spec["state"]:
        if s["name"] == "err":
            #print("Already contains state by the name err, skipping.")
            return old_spec

    spec["state"].append({"name":"err","type":"Bool"})

    se = spec["states_equal"]["definition"]
    spec["states_equal"]["definition"] = "(or (and err_1 err_2) (and (not err_1) (not err_2)\n" + se + "\n))"

    for m in spec["methods"]:
        req = m["requires"]
        ens = m["ensures"]
        m["requires"] = "true"
        m["ensures"] = ("(or (and err err_new)\n" +
                        "    (and (not err) (not err_new) " + req + " " + ens + ")\n" +
                        "    (and (not err) err_new (not " + req + ")))")

    return Specification(spec)

# spec = fileToSpec(None)
# spec = lifeSpecification(spec)
# s = yaml.dump(spec, default_flow_style=False)
# print(s)
