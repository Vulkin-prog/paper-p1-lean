#!/usr/bin/env python3
"""Exact V18 biquadratic auxiliary certificate; Python standard library only.

This is a finite symbolic check, not a proof of the uniform estimates.
The four-block data are deliberately not constant-remainder motifs.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import gcd, lcm
from functools import reduce
import json


def clean(p):
    return {m: Q(c) for m, c in p.items() if c}


def add(*ps):
    out = {}
    for p in ps:
        for m, c in p.items():
            out[m] = out.get(m, Q(0)) + c
    return clean(out)


def scale(p, c):
    return clean({m: c * a for m, a in p.items()})


def mul(p, q):
    out = {}
    for (i, j), a in p.items():
        for (k, ell), b in q.items():
            m = (i + k, j + ell)
            out[m] = out.get(m, Q(0)) + a * b
    return clean(out)


def linprod(xs, ys):
    p = {(0, 0): Q(1)}
    for a in sorted(xs):
        p = mul(p, {(1, 0): Q(1), (0, 0): Q(a)})
    for b in sorted(ys):
        p = mul(p, {(0, 1): Q(1), (0, 0): Q(b)})
    return p


def root_series(offsets, order):
    ans = [Q(1)] + [Q(0)] * order
    for a in sorted(offsets):
        factor = [Q(1)]
        for n in range(1, order + 1):
            factor.append(factor[-1] * (Q(1, 2) - (n - 1)) * a / n)
        ans = [sum(ans[j] * factor[n - j] for j in range(n + 1))
               for n in range(order + 1)]
    return ans


def solve(matrix, rhs):
    a = [list(row) + [b] for row, b in zip(matrix, rhs)]
    rows, cols = len(a), len(matrix[0])
    pivots = []
    rr = 0
    for cc in range(cols):
        pp = next((i for i in range(rr, rows) if a[i][cc]), None)
        if pp is None:
            continue
        a[rr], a[pp] = a[pp], a[rr]
        lead = a[rr][cc]
        a[rr] = [x / lead for x in a[rr]]
        for ii in range(rows):
            if ii != rr and a[ii][cc]:
                t = a[ii][cc]
                a[ii] = [x - t * y for x, y in zip(a[ii], a[rr])]
        pivots.append(cc)
        rr += 1
        if rr == rows:
            break
    for row in a:
        if not any(row[:cols]) and row[-1]:
            raise ValueError("Fixed constant fourth coefficient is inconsistent.")
    x = [Q(0)] * cols
    for ii, cc in enumerate(pivots):
        x[cc] = a[ii][-1]
    assert all(sum(c * z for c, z in zip(row, x)) == b
               for row, b in zip(matrix, rhs))
    return x, len(pivots)


def fmt(p):
    return {f"X^{i}Y^{j}": str(c)
            for (i, j), c in sorted(p.items(), key=lambda z: (sum(z[0]), z[0]))}


def sqroot_remainder(offsets):
    """Return degree of P-A^2 for the monic polynomial part of sqrt(P)."""
    r = len(offsets) // 2
    coeffs = root_series(offsets, r)
    a = {(r - n, 0): coeffs[n] for n in range(r + 1)}
    rem = add(linprod(offsets, []), scale(mul(a, a), -1))
    return max((i for i, j in rem), default=-1)


def main():
    I1, I2 = {0, 1, 3, 7}, {0, 1, 4, 8}
    J1, J2 = {-1, 0, 2, 6}, {-1, 0, 4, 7}
    Is = [set(), I1, I2, I1 ^ I2]
    Js = [set(), J1, J2, J1 ^ J2]
    q = 2
    k = 3 * q
    order = 2 * k + 2
    rs = [len(x) // 2 for x in Is]
    ss = [len(x) // 2 for x in Js]
    psis = [root_series(x, order) for x in Is]
    phis = [root_series(x, order) for x in Js]
    rows = [(i, n - i) for n in range(2 * k + 1) for i in range(n + 1)]
    columns = [(chi, i, j) for chi in range(3)
               for i in range(k - rs[chi] + 1)
               for j in range(k - ss[chi] + 1)]

    def coeff(chi, i, j, u, v):
        a, b = u - (k - i - rs[chi]), v - (k - j - ss[chi])
        if a < 0 or b < 0:
            return Q(0)
        return psis[chi][a] * phis[chi][b]

    matrix = [[coeff(chi, i, j, u, v) for chi, i, j in columns]
              for u, v in rows]
    rhs = [-coeff(3, 0, 0, u, v) for u, v in rows]
    solution, rank = solve(matrix, rhs)
    den = lcm(*(x.denominator for x in solution))
    raw = [int(x * den) for x in solution] + [den]
    content = reduce(gcd, (abs(x) for x in raw if x))
    raw = [x // content for x in raw]
    As = [{}, {}, {}, {(0, 0): Q(raw[-1])}]
    for (chi, i, j), c in zip(columns, raw):
        if c:
            As[chi][i, j] = Q(c)
    assert As[3] and list(As[3]) == [(0, 0)]
    # A nonzero constant coefficient certifies no common nonconstant factor.

    residual = {}
    for n in range(order + 1):
        for u in range(n + 1):
            v = n - u
            c = sum(a * coeff(chi, i, j, u, v)
                    for chi in range(4) for (i, j), a in As[chi].items())
            if c:
                residual[u, v] = c
    assert not any(i + j <= 2 * k for i, j in residual)
    first_degree = min(i + j for i, j in residual)
    assert first_degree >= 2 * k + 1

    Fs = [linprod(Is[i], Js[i]) for i in range(4)]
    G = linprod(I1 & I2, J1 & J2)
    F1G = linprod(I1 - I2, J1 - J2)
    F2G = linprod(I2 - I1, J2 - J1)
    assert mul(Fs[1], Fs[2]) == mul(mul(G, G), Fs[3])
    assert mul(G, F1G) == Fs[1]
    assert mul(G, F2G) == Fs[2]

    U = add(mul(As[0], As[0]), mul(mul(As[1], As[1]), Fs[1]),
            scale(mul(mul(As[2], As[2]), Fs[2]), -1),
            scale(mul(mul(As[3], As[3]), Fs[3]), -1))
    V = add(mul(As[0], As[1]), scale(mul(mul(As[2], As[3]), F2G), -1))
    R = add(mul(U, U), scale(mul(Fs[1], mul(V, V)), -4))
    assert R
    assert all(c.denominator == 1 for c in R.values())
    assert max(i for i, j in R) <= 4 * k
    assert max(j for i, j in R) <= 4 * k
    assert max(i + j for i, j in R) <= 8 * k

    # Direct multiplication of the four sign conjugates in the integral basis.
    def basis_product(i, j):
        if i == 0:
            return j, {(0, 0): Q(1)}
        if j == 0:
            return i, {(0, 0): Q(1)}
        if i == j:
            return 0, Fs[i]
        ii, jj = sorted((i, j))
        if (ii, jj) == (1, 2):
            return 3, G
        if (ii, jj) == (1, 3):
            return 2, F1G
        return 1, F2G

    def algebra_mul(a, b):
        out = [{}, {}, {}, {}]
        for i in range(4):
            for j in range(4):
                h, factor = basis_product(i, j)
                out[h] = add(out[h], mul(mul(a[i], b[j]), factor))
        return out

    product = [{(0, 0): Q(1)}, {}, {}, {}]
    for s1, s2 in [(1, 1), (1, -1), (-1, 1), (-1, -1)]:
        conjugate = [As[0], scale(As[1], s1), scale(As[2], s2),
                     scale(As[3], s1 * s2)]
        product = algebra_mul(product, conjugate)
    assert product == [R, {}, {}, {}]

    block_remainder_degrees = [sqroot_remainder(x) for x in [I1, J1, I2, J2]]
    assert all(d == 1 for d in block_remainder_degrees)

    payload = {
        "status": "ALL CHECKS PASS",
        "date": "2026-10-31",
        "arithmetic": "Exact Fraction arithmetic; Python standard library only.",
        "scope": "Finite symbolic illustration, no asymptotic or integer-point claim.",
        "q": q, "k": k,
        "I1": sorted(I1), "J1": sorted(J1), "I2": sorted(I2), "J2": sorted(J2),
        "all_four_individual_square_remainders_have_degree": block_remainder_degrees,
        "full_homogeneous_unknown_count": sum((k-r+1)*(k-s+1) for r,s in zip(rs,ss)),
        "constraint_count": len(rows),
        "unknown_count_with_A3_fixed_to_one": len(columns),
        "matrix_rank": rank,
        "primitive_coefficient_certificate": "A3 is a nonzero constant.",
        "A3_constant": str(As[3][0, 0]),
        "auxiliary_coefficients": [fmt(p) for p in As],
        "all_total_degrees_through_2k_cancel": True,
        "first_residual_total_degree": first_degree,
        "first_residual_homogeneous_part": fmt({m:c for m,c in residual.items()
                                               if sum(m)==first_degree}),
        "direct_four_conjugate_product_equals_explicit_norm": True,
        "norm_nonzero": True,
        "norm_degree_X": max(i for i,j in R),
        "norm_degree_Y": max(j for i,j in R),
        "norm_total_degree": max(i+j for i,j in R),
        "norm_height": str(max(abs(c.numerator) for c in R.values())),
        "norm_nonzero_coefficient_count": len(R),
        "norm_coefficients": fmt(R),
    }
    dest = Path(__file__).with_name("biquadratic_certificate.json")
    dest.write_text(json.dumps(payload, ensure_ascii=False, indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:payload[k] for k in [
        "status","q","k","constraint_count","unknown_count_with_A3_fixed_to_one",
        "matrix_rank","A3_constant","first_residual_total_degree",
        "norm_degree_X","norm_degree_Y","norm_total_degree",
        "norm_nonzero_coefficient_count"]},indent=2))


if __name__ == "__main__":
    main()
