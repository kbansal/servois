from parser import *
from lift import *

spec = fileToSpec(None)
spec = liftSpec(spec)
s = yaml.dump(spec.spec, default_flow_style=False)
print(s)
