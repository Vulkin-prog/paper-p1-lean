#!/usr/bin/env python3
"""Exact finite algebra diagnostics for the channel and triple sections.

This reproduces the calculations run during the V1.3 authoring review.
All calculations use integer or Fraction arithmetic.  The finite searches
are diagnostics of identities and examples; they do not establish the
asymptotic estimates or replace the written proof of the 19/30 inequality.

Run with Python 3, without third-party dependencies:
    python3 diagnostics/channel_and_triple_checks.py

The JSON result is written next to this script by default.  An optional
--output argument selects another destination.
"""

from argparse import ArgumentParser
from fractions import Fraction
from math import gcd
from pathlib import Path
import json


def channel_sum(a, b, length):
    return sum(
        (1 if d == 1 else 2 ** (d - 2))
        * (length - 1 - a * d)
        * (length - 1 - b * d)
        for d in range(1, length // b + 1)
    )


def run_checks():
    counts = {
        "finite_channel_identities": 0,
        "phase_constants": 0,
        "rational_density_triples": 0,
        "positive_witness_nullities": 0,
    }

    for length in range(5, 151):
        for b in range(3, 11):
            for a in range(b // 2 + 1, b):
                if gcd(a, b) != 1:
                    continue
                q, r = divmod(length, b)
                direct = channel_sum(a, b, length)
                if q >= 1:
                    closed = (
                        2 ** (q - 1)
                        * (
                            (b - a) * (b + r - 1) * q
                            + (r - 1) ** 2
                            + (a + b) * (r - 1)
                            + 3 * a * b
                        )
                        - (a + b) * (length - 1)
                        - a * b
                    )
                    assert direct == closed, (a, b, length, direct, closed)
                    counts["finite_channel_identities"] += 1

        q, r = divmod(length, 5)
        direct = (
            Fraction(2, 15) * channel_sum(3, 5, length)
            + Fraction(3, 10) * channel_sum(4, 5, length)
        )
        closed = Fraction(
            2 ** (q - 1)
            * (17 * (r + 4) * q + 13 * r * r + 87 * r + 620)
            - 113 * length
            - 127,
            30,
        )
        assert direct == closed, (length, direct, closed)
        counts["finite_channel_identities"] += 1

    for b, expected in (
        (4, Fraction(1, 24)),
        (5, Fraction(17, 300)),
        (6, Fraction(1, 45)),
    ):
        constant = sum(
            Fraction((2 * a - b) * (b - a), a)
            for a in range(b // 2 + 1, b)
            if gcd(a, b) == 1
        ) / (b * b)
        assert constant == expected, (b, constant, expected)
        counts["phase_constants"] += 1

    maximum = (Fraction(0), (0, 0, 0))
    for u in range(2, 150):
        for v in range(u + 1, 2 * u):
            for w in range(v + 1, 2 * u):
                if gcd(gcd(u, v), w) != 1:
                    continue
                density = Fraction(gcd(u, v), v) + Fraction(
                    gcd(u, w) + gcd(v, w) - 1, w
                )
                assert density <= Fraction(19, 30), (u, v, w, density)
                counts["rational_density_triples"] += 1
                if density > maximum[0]:
                    maximum = (density, (u, v, w))

    for length in range(31, 301):
        normalized_sets = [
            set(multiplier * j for j in range(-1, length))
            for multiplier in (6, 5, 4)
        ]
        actual = 3 * length - (len(set.union(*normalized_sets)) - 1)
        formula = (
            (length - 1) // 6
            + (length - 1) // 3
            + (length - 1) // 5
            - (length - 1) // 15
        )
        assert actual == formula, (length, actual, formula)
        counts["positive_witness_nullities"] += 1

    return {
        "status": "PASS",
        "checks": counts,
        "maximum_finite_rational_density": str(maximum[0]),
        "attaining_example": maximum[1],
        "scope": (
            "Finite identities and representative finite arithmetic checks; "
            "not proof of the asymptotic estimates."
        ),
    }


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_suffix(".json"),
    )
    args = parser.parse_args()
    result = run_checks()
    rendered = json.dumps(result, indent=2) + "\n"
    args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
