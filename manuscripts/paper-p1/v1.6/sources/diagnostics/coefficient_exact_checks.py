#!/usr/bin/env python3
"""Exact finite checks of coefficient identities; not asymptotic proof checks."""
import json
import math
from fractions import Fraction as F
from pathlib import Path


def weight(d):
    return 1 if d == 1 else 2 ** (d - 2)


def channel(a, b, L, sign):
    return sum(weight(d) * (L + sign - a*d) * (L + sign - b*d)
               for d in range(1, L//b + 1))


def closed(a, b, L, sign):
    m, r = divmod(L, b)
    if m == 0:
        return 0
    return (2**(m-1)*((b-a)*(b+r+sign)*m + (r+sign)**2
                      + (a+b)*(r+sign) + 3*a*b)
            - (a+b)*(L+sign) - a*b)


count = 0
for b in range(2, 13):
    for a in range(1, b):
        if math.gcd(a, b) != 1:
            continue
        for L in range(1, 97):
            for sign in (-1, 1):
                assert channel(a, b, L, sign) == closed(a, b, L, sign)
                count += 1

# Each selection of diameter D has exactly one predecessor placement.
placements = 0
for L in range(1, 101):
    for D in range(0, L+1):
        signs = [-1] + [1]*(L-D)
        assert sum(signs) == L-1-D
        placements += 1

# With integer mean m, remove the common e^{-m} from the Poisson masses.
# The second difference is negative exactly between its two real roots.
charlier = []
for m, expected in [(1, F(3)), (2, F(10, 3))]:
    pi = lambda k: F(m**k, math.factorial(k)) if k >= 0 else F(0)
    negative = [k for k in range(4*m+10) if k*(k-1)-2*m*k+m*m < 0]
    masses = [pi(k-2)-2*pi(k-1)+pi(k) for k in negative]
    norm_coefficient = -2*sum(masses, F(0))
    assert norm_coefficient == expected
    a, b = min(negative), max(negative)
    telescope = 2*(pi(b-1)-pi(b)+pi(a-1)-pi(a-2))
    assert telescope == expected
    charlier.append({'mean':m, 'negative_indices':negative,
                     'norm_over_exp_minus_mean':str(expected)})

result = {
    'status':'passed',
    'scope':'Finite exact algebra only; these checks do not verify the arithmetic asymptotics or the main theorem.',
    'channel_identity_cases':count,
    'signed_placement_cases':placements,
    'charlier_cases':charlier,
    'unit_mean_tv_coefficient_over_exp_minus_one':str(F(1,9)*F(3)*F(1,4))
}
assert result['unit_mean_tv_coefficient_over_exp_minus_one'] == '1/12'
p = Path(__file__).with_suffix('.json')
p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
