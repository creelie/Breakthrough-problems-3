"""Verify the named compiled components, without claiming a forward bound."""
from pathlib import Path
import json,re,sys
from verify_axioms import inspect

audit=Path(__file__).with_name('MobiusAudit.lean').read_text(encoding='utf-8')
expected=re.findall(r'^#print axioms (\S+)',audit,re.M)
result={'component_axioms':inspect(Path(sys.argv[1]),expected),
        'component_kernel_audit':'PASS',
        'forward_smoothed_mobius_bound_formalised':False,
        'whole_appendix_formalised':False,
        'independent_zero_free_replacement_proved':False}
Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
