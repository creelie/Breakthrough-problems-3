"""Exact exponent and residue-symbol controls, not an analytic estimate."""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


records = []
for a in (F(1), F(21, 20), F(11, 10), F(6, 5), F(5, 4), F(2)):
    theta, err = F(1, 2) + F(5, 12) * a, 1 - a / 6
    assert (theta < 1) == (a < F(6, 5))
    assert theta > err
    records.append({'alpha': str(a), 'main_exponent': str(theta),
                    'row_error_exponent': str(err), 'power_saving_if_input_proved': theta < 1})
assert F(1, 2) + F(5, 12) * F(21, 20) == F(15, 16)
assert 1 - F(21, 20) / 6 == F(33, 40)

# Exact finite-field check of the sixth-power row identity. No floating roots.
count = 0
for p in range(37, 201):
    if p % 6 != 1 or not prime(p):
        continue
    for a in range(1, 7):
        assert a < p and pow(a ** 6, (p - 1) // 6, p) == 1
        count += 1

# The generic-coefficient shortcut has an asymptotic exponent obstruction.
a, e = F(21, 20), F(1, 32)
gap = (2 + a / 6) - (1 + a + e)
assert gap == F(3, 32) > 0
result = {'status': 'PASS', 'parameter_cases': records,
          'finite_sixth_power_residue_checks': count,
          'generic_coefficient_counterexample_exponent_gap': str(gap),
          'mean_square_input_proved': False,
          'independent_zero_free_theorem_proved': False}
out = Path(__file__).parent / 'verification'
out.mkdir(exist_ok=True)
(out / 'mean-square-controls.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print(json.dumps(result, indent=2))
