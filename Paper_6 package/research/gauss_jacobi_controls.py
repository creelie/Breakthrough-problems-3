"""Exact cubic Gauss/Jacobi arithmetic; no analytic cancellation claim."""
from pathlib import Path
from math import isqrt
import json

ZERO=(0,0)
ROOTS=((1,0),(0,1),(-1,-1))
def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))
def add(x,y):return x[0]+y[0],x[1]+y[1]
def mul(x,y):
    a,b=x;c,d=y
    return a*c-b*d,a*d+b*c-b*d
def conv(a,b):
    p=len(a);out=[ZERO]*p
    for i,x in enumerate(a):
        if x==ZERO:continue
        for j,y in enumerate(b):
            if y!=ZERO:out[(i+j)%p]=add(out[(i+j)%p],mul(x,y))
    return out

records=[]
for p in range(7,200):
    if p%3!=1 or not prime(p):continue
    # A primitive root is checked by explicitly enumerating its whole orbit.
    for g in range(2,p):
        powers=[pow(g,j,p) for j in range(p-1)]
        if len(set(powers))==p-1:break
    else:raise AssertionError(p)
    logs={x:j for j,x in enumerate(powers)}
    exps={x:j%3 for x,j in logs.items()}
    G=[ZERO]+[ROOTS[exps[x]] for x in range(1,p)]
    J=ZERO
    for x in range(1,p):
        y=(1-x)%p
        if y:J=add(J,ROOTS[(exps[x]+exps[y])%3])
    a,b=J
    assert a*a-a*b+b*b==p
    w=pow(g,(p-1)//3,p)
    assert w!=1 and (w*w+w+1)%p==0
    assert (a+b*w)%p==0
    cube=conv(conv(G,G),G)
    cube[0]=add(cube[0],(-p*a,-p*b))
    assert len(set(cube))==1, 'G^3-pJ must be a multiple of Phi_p.'
    records.append({'p':p,'primitive_root':g,'J':[a,b], 'pi':[-a,-b],
                    'norm_J':p,'polynomial_cubic_identity':'PASS'})
result={'status':'PASS','prime_cases':len(records),'cases':records,
        'arithmetic_scope':'Finite exact controls for the written classical finite-field identity.',
        'mean_square_estimate_proved':False,'independent_zero_free_theorem_proved':False}
out=Path(__file__).parent/'verification';out.mkdir(exist_ok=True)
(out/'gauss-jacobi-controls.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':'PASS','prime_cases':len(records),'mean_square_estimate_proved':False}))
