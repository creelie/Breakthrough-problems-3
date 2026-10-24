"""Exact arithmetic checks for the 11/12 transfer; not a zero-free proof."""
from fractions import Fraction as F
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parent
theta=F(11,12);delta=F(1,2000);a=theta-2*delta;sigma=a+8*delta
prime=F(49,50);h=F(47,50);alpha=1-prime
assert F(1,2)<=a<=1 and 0<delta<F(1,1000)
assert a+2*delta==theta and sigma<1
assert 1+sigma-h<prime
assert h+F(1,100)<=prime
assert 1800*alpha==36 and 1800*alpha>34
assert 25*(1-sigma)>2
# These two old choices do not meet the new proof's required margins.
assert 700*alpha<34
assert 17*(1-sigma)<2
assert 150+441<=600
assert F(96*49,48)*F(3,2)<150 # log 2 > 2/3; j>=48.
assert F(24)*F(81,56)+1<36 # log 2 > 56/81, log q > 1.
assert 72*F(7,10)<51 # 2 log 2 J <= 51 log q; use a safe round-up.
# Use 56 log q, rather than 55, to absorb this and the 5 log q term.
assert 56*11+1==617
report={'theta':str(theta),'delta':str(delta),'sigma0':str(sigma),
        'prime_exponent':str(prime),'unsmoothing_exponent':str(h),
        'prime_exponent_margin':str(prime-(1+sigma-h)),
        'smoothness_cutoff_power':1800,'major_arc_margin':str(1800*alpha-34),
        'cyclotomic_cutoff_power':25,'tail_margin':str(25*(1-sigma)-2),
        'block_denominator':48,'block_constant':600,'progression_constant':600*617,
        'old_700_cutoff_fails_new_major_arc_margin':True,
        'old_17_cutoff_fails_new_tail_margin':True,
        'zero_free_theorem_proved_by_this_program':False,'status':'PASS'}
(ROOT/'parameter-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
