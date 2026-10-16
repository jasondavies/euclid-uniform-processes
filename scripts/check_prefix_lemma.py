"""Exhaustive check of the Euclidean-prefix lemma (Lean: ShortGCD.prefix_pairs_distinct).

For every coprime pair with 3 <= a < A and 1 <= b < a, every prefix length h,
and up to the requested number of consecutive moduli above 2a / r_h (with
m < 4a), check that the pairs (r_i mod m, r_{i+1} mod m), 0 <= i < h, are
distinct. Any failure produces a nonzero exit status and a counterexample.
As a control, it also counts collisions when the hypothesis is dropped.

    python3 scripts/check_prefix_lemma.py [A] [moduli per prefix]
"""

import sys
from math import gcd


def remainders(a, b):
    rs = [a, b]
    while rs[-1]:
        rs.append(rs[-2] % rs[-1])
    rs.pop()
    return rs


def main(limit=1500, width=60, control_limit=400):
    checked = failures = 0
    first_failure = None
    for a in range(3, limit):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            rs = remainders(a, b)
            for h in range(1, len(rs)):
                lo = 2 * a // rs[h] + 1
                for m in range(lo, min(lo + width, 4 * a)):
                    checked += 1
                    if len({(rs[i] % m, rs[i + 1] % m) for i in range(h)}) != h:
                        failures += 1
                        if first_failure is None:
                            first_failure = (a, b, h, m)
    print(f"instances checked: {checked}, failures: {failures}")
    if failures:
        raise SystemExit(f"Prefix lemma failed; first counterexample (a, b, h, m): {first_failure}")

    collisions = 0
    for a in range(3, control_limit):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            rs = remainders(a, b)
            for h in range(1, len(rs)):
                for m in range(2, 2 * a // rs[h] + 1):
                    if len({(rs[i] % m, rs[i + 1] % m) for i in range(h)}) != h:
                        collisions += 1
    print(f"control (hypothesis dropped, a < {control_limit}): {collisions} collisions")


if __name__ == "__main__":
    main(*map(int, sys.argv[1:3]))
