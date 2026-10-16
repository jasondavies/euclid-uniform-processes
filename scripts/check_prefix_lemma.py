"""Exhaustive check of the Euclidean-prefix lemma (Lean: ShortGCD.prefix_pairs_distinct).

For every coprime a > b with a < A, every prefix length h, and moduli m just
above the threshold 2a / r_h, the ordered pairs (r_i mod m, r_{i+1} mod m),
0 <= i < h, must be pairwise distinct. As a control, it also counts collisions
when the hypothesis is dropped, to show the test can fail.

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
    print(f"instances checked: {checked}, failures: {failures}")

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
