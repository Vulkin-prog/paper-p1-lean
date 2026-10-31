#!/usr/bin/env python3
"""Finite exact checks for the heterogeneous identities used in P1 V1.3.

No third-party packages are required. All probability and polynomial
calculations use fractions.Fraction. The joint laws include incompatible,
identical, affine, independent heterogeneous, and arbitrary dependent
Bernoulli variables. This checks finite algebra, not the arithmetic counting
lemmas, infinite norm bounds, or asymptotic Poisson approximation theorem.

Run:
    python3 diagnostics/heterogeneous_formal_checks.py

The JSON report is written next to this script, or to --output PATH.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
from itertools import combinations, product
import json
from math import comb, factorial
from pathlib import Path
import random
import sys


def normalize(weights):
    total = sum(weights.values())
    assert total > 0 and all(w >= 0 for w in weights.values())
    return {state: Q(weight, total) for state, weight in weights.items() if weight}


def add(a, b):
    result = [Q(0)] * max(len(a), len(b))
    for k, value in enumerate(a):
        result[k] += value
    for k, value in enumerate(b):
        result[k] += value
    return result


def conv(a, b, order=None):
    length = len(a) + len(b) - 1
    if order is not None:
        length = min(length, order + 1)
    result = [Q(0)] * length
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i + j < length:
                result[i + j] += x * y
    return result


def scale(a, coefficient):
    return [coefficient * value for value in a]


def padded(a, length):
    assert len(a) <= length
    return a + [Q(0)] * (length - len(a))


def falling(k, r):
    if k < r:
        return 0
    return factorial(k) // factorial(k - r)


def factorial_moment(masses, r):
    return sum((Q(falling(k, r)) * value for k, value in enumerate(masses)), Q(0))


def factorial_cumulants(moments):
    """Independent coefficient computation via G'=K'G for G=exp(K)."""
    result = [Q(0)] * len(moments)
    assert moments[0] == 1
    for r in range(1, len(moments)):
        result[r] = moments[r] - sum(
            (
                Q(comb(r - 1, j - 1)) * result[j] * moments[r - j]
                for j in range(1, r)
            ),
            Q(0),
        )
    return result


def delta_power(r):
    return [Q((-1) ** (r - k) * comb(r, k)) for k in range(r + 1)]


def outside_bernoulli_product(marginals, omitted):
    result = [Q(1)]
    for i, p in enumerate(marginals):
        if i not in omitted:
            result = conv(result, [1 - p, p])
    return result


def all_subsets(n):
    return [tuple(indices) for r in range(n + 1) for indices in combinations(range(n), r)]


def independent_heterogeneous():
    probabilities = [Q(1, 2), Q(1, 3), Q(1, 5), Q(2, 7), Q(3, 8)]
    law = {}
    for state in product((0, 1), repeat=len(probabilities)):
        weight = Q(1)
        for bit, p in zip(state, probabilities):
            weight *= p if bit else 1 - p
        law[state] = weight
    return law


def identical_events():
    return {(0,) * 5: Q(5, 7), (1,) * 5: Q(2, 7)}


def mutually_exclusive_events():
    weights = {(0,) * 5: 2}
    for i, weight in enumerate((1, 2, 3, 4, 5)):
        state = tuple(int(j == i) for j in range(5))
        weights[state] = weight
    return normalize(weights)


def affine_events():
    """Six overlapping affine events on five independent uniform bits."""
    counts = {}
    for x0, x1, x2, x3, x4 in product((0, 1), repeat=5):
        state = (
            int(x0 == 1),
            int(x1 == 0 and x2 == 1),
            int(x0 == 1 and x1 == 0),
            int(x0 == 0),
            int((x0 ^ x1 ^ x2) == 1 and x3 == 0),
            int(x4 == 1 and (x0 ^ x3) == 0 and (x1 ^ x2 ^ x4) == 1),
        )
        counts[state] = counts.get(state, 0) + 1
    return normalize(counts)


def arbitrary_dependent(n, seed):
    rng = random.Random(seed)
    return normalize({state: rng.randrange(0, 24) for state in product((0, 1), repeat=n)})


def check_joint_law(name, law):
    n = len(next(iter(law)))
    assert n >= 4
    assert sum(law.values()) == 1
    subsets = all_subsets(n)
    p = [sum((prob * state[i] for state, prob in law.items()), Q(0)) for i in range(n)]

    # Direct expectations. No centered-expansion identity is used here.
    centered = {}
    joint = {}
    for subset in subsets:
        c = Q(0)
        q = Q(0)
        for state, prob in law.items():
            centered_term = Q(1)
            joint_term = 1
            for i in subset:
                centered_term *= state[i] - p[i]
                joint_term *= state[i]
            c += prob * centered_term
            q += prob * joint_term
        centered[subset] = c
        joint[subset] = q

    actual = [Q(0)] * (n + 1)
    for state, prob in law.items():
        actual[sum(state)] += prob
    moments = [factorial_moment(actual, r) for r in range(5)]
    cumulants = factorial_cumulants(moments)
    mu = sum(p, Q(0))
    s2 = sum((x**2 for x in p), Q(0))
    s3 = sum((x**3 for x in p), Q(0))
    s4 = sum((x**4 for x in p), Q(0))
    C2 = sum((value for I, value in centered.items() if len(I) == 2), Q(0))
    C3 = sum((value for I, value in centered.items() if len(I) == 3), Q(0))
    C4 = sum((value for I, value in centered.items() if len(I) == 4), Q(0))
    A2 = sum((abs(value) for I, value in centered.items() if len(I) == 2), Q(0))

    alpha_formula = 2 * C2 - s2
    cubic_diagonal = sum(((p[i] + p[j]) * centered[(i, j)] for i, j in combinations(range(n), 2)), Q(0))
    quartic_triples = sum(
        (sum((p[i] for i in I), Q(0)) * centered[I] for I in combinations(range(n), 3)), Q(0)
    )
    quartic_pairs = sum(
        ((p[i] ** 2 + p[i] * p[j] + p[j] ** 2) * centered[(i, j)] for i, j in combinations(range(n), 2)),
        Q(0),
    )
    cubic_formula = 6 * C3 - 6 * cubic_diagonal + 2 * s3
    quartic_formula = 24 * C4 - 12 * C2**2 - 24 * quartic_triples + 24 * quartic_pairs - 6 * s4

    # Convolution on actual point masses in z, independently of moments.
    full_expansion = [Q(0)] * (n + 1)
    B2 = padded(outside_bernoulli_product(p, ()), n + 1)
    for I in subsets:
        term = scale(conv(delta_power(len(I)), outside_bernoulli_product(p, I)), centered[I])
        full_expansion = add(full_expansion, term)
        if len(I) == 2:
            B2 = add(B2, term)
    B2_moments = [factorial_moment(B2, r) for r in range(5)]
    B2_cumulants = factorial_cumulants(B2_moments)

    # The compressed display in quartic_lower.tex, checked as formal series
    # in t at order four using exact inverses of (1+p_i t).
    base = [Q(1)]
    for value in p:
        base = conv(base, [Q(1), value], order=4)
    bracket = [Q(1), Q(0), Q(0), Q(0), Q(0)]
    for I in subsets:
        if not 2 <= len(I) <= 4:
            continue
        inverse = [Q(1)]
        for i in I:
            inverse = conv(inverse, [(-p[i]) ** j for j in range(5)], order=4)
        shifted = [Q(0)] * len(I) + scale(inverse, centered[I])
        bracket = add(bracket, shifted[:5])[:5]
    quotient_reconstruction = padded(conv(base, bracket, order=4), 5)
    true_factorial_series = [moments[r] / factorial(r) for r in range(5)]

    checks = {
        "mean_from_marginals": mu == moments[1],
        "singletons_center_to_zero": all(centered[(i,)] == 0 for i in range(n)),
        "full_centered_measure_identity": full_expansion == actual,
        "alpha_equals_2C2_minus_s2": alpha_formula == cumulants[2],
        "heterogeneous_kappa3_identity": cubic_formula == cumulants[3],
        "heterogeneous_kappa4_identity": quartic_formula == cumulants[4],
        "B2_mass_one": sum(B2) == 1,
        "B2_mean_exact": B2_moments[1] == moments[1],
        "B2_second_factorial_moment_exact": B2_moments[2] == moments[2],
        "B2_alpha_exact": B2_cumulants[2] == alpha_formula,
        "B2_cubic_without_distinct_triples": B2_cumulants[3] == -6 * cubic_diagonal + 2 * s3,
        "B2_quartic_without_distinct_triples_or_quadruples": B2_cumulants[4] == -12 * C2**2 + 24 * quartic_pairs - 6 * s4,
        "formal_factorial_quotient_to_degree_four": quotient_reconstruction == true_factorial_series,
        "quadratic_reference_first_two_factorial_moments": B2_moments[2] == mu**2 + alpha_formula,
    }
    failed = [key for key, passed in checks.items() if not passed]
    if failed:
        raise AssertionError(f"{name}: failed {failed}")
    incompatible_positive_triples = [
        list(I) for I in combinations(range(n), 3) if joint[I] == 0 and centered[I] > 0
    ]
    return {
        "name": name,
        "number_of_variables": n,
        "positive_joint_atoms": len(law),
        "marginals": [str(value) for value in p],
        "mu": str(mu),
        "alpha": str(alpha_formula),
        "kappa3": str(cumulants[3]),
        "kappa4": str(cumulants[4]),
        "signed_pair_activity": str(C2),
        "absolute_pair_activity": str(A2),
        "negative_B2_mass_positions": [k for k, value in enumerate(B2) if value < 0],
        "incompatible_triples_with_positive_centered_coefficient": incompatible_positive_triples,
        "checks": checks,
        "all_passed": all(checks.values()),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    cases = [
        ("independent_heterogeneous", independent_heterogeneous()),
        ("five_identical_events", identical_events()),
        ("five_mutually_exclusive_events", mutually_exclusive_events()),
        ("six_overlapping_affine_events_on_five_bits", affine_events()),
        ("arbitrary_dependent_n4_seed1304", arbitrary_dependent(4, 1304)),
        ("arbitrary_dependent_n5_seed1305", arbitrary_dependent(5, 1305)),
        ("arbitrary_dependent_n6_seed1306", arbitrary_dependent(6, 1306)),
        ("arbitrary_dependent_n6_seed1313", arbitrary_dependent(6, 1313)),
    ]
    reports = [check_joint_law(name, law) for name, law in cases]
    summary = {
        "document": "P1 V1.3",
        "diagnostic": "Exact finite heterogeneous Bernoulli identities",
        "arithmetic": "fractions.Fraction; no floating point arithmetic",
        "python_version": sys.version.split()[0],
        "scope": "Eight finite joint Bernoulli laws with four to six variables, including dependent and incompatible events.",
        "limitations": [
            "A finite diagnostic of algebraic identities, not a proof of them for every joint law.",
            "Does not test any arithmetic window-counting estimate or a growing-order asymptotic bound.",
            "Does not numerically certify the Bernoulli-to-Poisson convolution-norm inequality.",
            "Does not certify the optimal Poisson approximation exponent.",
        ],
        "number_of_cases": len(reports),
        "checks_per_case": len(reports[0]["checks"]),
        "total_checks": sum(len(case["checks"]) for case in reports),
        "all_passed": all(case["all_passed"] for case in reports),
        "cases": reports,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({key: summary[key] for key in ("number_of_cases", "total_checks", "all_passed")}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
