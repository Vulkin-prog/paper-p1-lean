"""Finite rational checks of the stopped identities; no asymptotic claim."""
from fractions import Fraction as F
from itertools import combinations
from math import comb
from pathlib import Path
import json


def add(*vectors):
    result = [F(0)] * max(map(len, vectors), default=0)
    for v in vectors:
        for i, x in enumerate(v):
            result[i] += x
    return result


def scale(c, vector):
    return [c * x for x in vector]


def conv(a, b):
    result = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return result


def power(a, k):
    result = [F(1)]
    for _ in range(k):
        result = conv(result, a)
    return result


def equal(a, b):
    size = max(len(a), len(b))
    return a + [F(0)] * (size - len(a)) == b + [F(0)] * (size - len(b))


def subsets(mask):
    result = []
    sub = mask
    while True:
        result.append(sub)
        if sub == 0:
            return result
        sub = (sub - 1) & mask


delta = [F(-1), F(1)]
counts = {}
for n in range(1, 5):
    admissible = 0
    checked = 0
    for code in range(1, 1 << (1 << n), 2):
        family = {s for s in range(1 << n) if code >> s & 1}
        if any(any(t not in family for t in subsets(s)) for s in family):
            continue
        admissible += 1
        boundary = [
            s for s in range(1, 1 << n)
            if s not in family and (s ^ (1 << (s.bit_length() - 1))) in family
        ]
        for state in range(1 << n):
            lhs = [F(0)] * (n + 1)
            lhs[state.bit_count()] = F(1)
            retained = [F(0)]
            remainder = [F(0)]
            for s in family:
                if s & state == s:
                    retained = add(retained, power(delta, s.bit_count()))
            for s in boundary:
                if s & state == s:
                    suffix = (state >> s.bit_length()).bit_count()
                    kernel = [F(0)] * suffix + [F(1)]
                    remainder = add(
                        remainder, conv(power(delta, s.bit_count()), kernel)
                    )
            assert equal(lhs, add(retained, remainder)), (n, family, state)
            checked += 1
    counts[str(n)] = {"hereditary_classes": admissible, "indicator_states": checked}

# A repeated source with a fully dependent suffix.
theta = F(1, 7)
lhs = add([F(1) - theta, F(0), F(0), theta],
          scale(-1, [F(1) - 3 * theta, 3 * theta]))
rhs = scale(theta, conv(power(delta, 2), [F(2), F(1)]))
assert equal(lhs, rhs)
assert sum(map(abs, lhs)) == 6 * theta

# A finite F_2 model with one retained pair and higher residual dependencies.
vectors = [1, 1, 2, 3]
n = len(vectors)
p = F(1, 2)
edge = 0b0011


def rank(mask):
    basis = {}
    for i, v in enumerate(vectors):
        if not (mask >> i & 1):
            continue
        while v:
            j = v.bit_length() - 1
            if j not in basis:
                basis[j] = v
                break
            v ^= basis[j]
    return len(basis)


q = {s: F(1, 1 << rank(s)) for s in range(1 << n)}
direct = {s for s in q if rank(s) == s.bit_count()}
gamma = {
    s for s in q if not (s & edge)
    and rank(edge | s) == 1 + s.bit_count()
}
family = direct | {edge | s for s in gamma}
retained = [F(0)]
for s in family:
    retained = add(retained, scale(q[s], power(delta, s.bit_count())))
Fr = [sum(p ** r for s in q if s.bit_count() == r and s not in direct)
      for r in range(n + 1)]
Gr = [F(0), F(0)] + [
    q[edge] * p ** (r - 2)
    * (comb(n - 2, r - 2) - sum(s.bit_count() == r - 2 for s in gamma))
    for r in range(2, n + 1)
]
b = [1 - p, p]
reference = add(power(b, n), scale(q[edge], conv(power(delta, 2), power(b, n - 2))))
deficit = [F(0)]
for r in range(n + 1):
    deficit = add(deficit, scale(Fr[r] + Gr[r], power(delta, r)))
assert equal(retained, add(reference, scale(-1, deficit)))

# Exact integer minimizers in the positivity criterion.
positivity_checks = []
for mu in [F(1, 3), F(1), F(5, 2), F(7)]:
    floor_mu = mu.numerator // mu.denominator
    fractional = mu - floor_mu
    k_min = floor_mu if fractional == 0 else floor_mu + 1
    minimum = (k_min - mu) ** 2 - k_min
    assert minimum == -mu - fractional * (1 - fractional)
    alpha_star = 2 * mu ** 2 / (-minimum)
    assert 1 + alpha_star * minimum / (2 * mu ** 2) == 0
    assert 1 + (alpha_star + F(1, 10)) * minimum / (2 * mu ** 2) < 0
    positivity_checks.append({"mu": str(mu), "threshold": str(alpha_star)})

result = {
    "status": "passed",
    "scope": "Finite exact rational identities, not asymptotic estimates or proof certification.",
    "ordered_boundary": counts,
    "fully_dependent_suffix": "norm = 6 theta; stopped upper bound = 12 theta",
    "retained_pair_reference": {
        "vectors": vectors,
        "F_r": list(map(str, Fr)),
        "G_r": list(map(str, Gr)),
        "identity": "T_D = B_beta - sum (F_r+G_r) Delta^r",
    },
    "positivity_minimizers": positivity_checks,
}
out = Path(__file__).with_suffix(".json")
out.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
