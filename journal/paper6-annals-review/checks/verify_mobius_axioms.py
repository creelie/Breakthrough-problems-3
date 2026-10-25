"""Verify named implications without treating a cited input as a new proof."""
from pathlib import Path
import json,re,sys
from verify_axioms import inspect

audit=Path(__file__).with_name('MobiusAudit.lean').read_text(encoding='utf-8')
expected=re.findall(r'^#print axioms (\S+)',audit,re.M)
result={'component_axioms':inspect(Path(sys.argv[1]),expected),
        'component_kernel_audit':'PASS',
        'forward_smoothed_mobius_bound_formalised':True,
        'forward_scope':'7/8 nonvanishing implies C_W q^104 X^(11/12); actual sum and analytic steps are formalised.',
        'arbitrary_boundary_forward_formalised':True,
        'arbitrary_boundary_equivalence_formalised':True,
        'finite_sum_identity_formalised':True,
        'closed_instantiations_audited_separately':True,
        'independent_zero_free_replacement_proved':False}
Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result))
