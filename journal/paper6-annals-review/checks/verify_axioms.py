"""Reject extra axioms and missing endpoint statements; never infer a proof from examples."""
from pathlib import Path
import argparse, json, re

def inspect(log, expected):
    text=Path(log).read_text(encoding='utf-8')
    entries={}
    for name, body in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S):
        entries[name]=set(re.findall(r'[A-Za-z_][A-Za-z0-9_.]*',body))
    for name in re.findall(r"'([^']+)' does not depend on any axioms",text):
        entries[name]=set()
    assert set(entries)==set(expected), f'Missing or unexpected theorem reports: {set(expected)^set(entries)}'
    allowed={'propext','Classical.choice','Quot.sound'}
    assert all(a<=allowed for a in entries.values()), 'Unexpected proof axiom'
    assert not re.search(r'\b(sorryAx|ofReduceBool)\b',text), 'Unaccepted proof shortcut'
    return {n:sorted(a) for n,a in entries.items()}

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('endpoint_log');p.add_argument('original_log');p.add_argument('output')
    a=p.parse_args(); root=Path(__file__).resolve().parents[3]
    original=re.findall(r'^#print axioms (\S+)',(root/'lean/Axioms.lean').read_text(),re.M)
    endpoints=re.findall(r'^#print axioms (\S+)',Path(__file__).with_name('EndpointAudit.lean').read_text(),re.M)
    result={'status':'PASS','endpoint_axioms':inspect(a.endpoint_log,endpoints),
            'original_axioms':inspect(a.original_log,original),
            'scope':'Exact compiled formal statements and their axiom closures. This is not an independent zero-free proof or a formalisation of every line of the written 11/12 supplement.',
            'independent_zero_free_replacement_proved':False}
    Path(a.output).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result))
