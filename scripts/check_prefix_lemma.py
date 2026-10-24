"""Finite check of the Euclidean-prefix lemma (Lean: ShortGCD.prefix_class_card_le_three).

For every coprime pair with 3 <= a < A and 1 <= b < a, every prefix length h,
and up to the requested number of consecutive moduli above 2a / r_h (with
m < 4a), check that each residue class modulo m contains at most three of
r_0, ..., r_h. Any failure produces a nonzero exit status and a counterexample.
It also counts the instances with a class of exactly three values, showing that
the bound is attained, and, as a control, the instances with a class of four or
more values when the hypothesis is dropped.

    python3 scripts/check_prefix_lemma.py [A] [moduli per prefix]
"""

import sys
from collections import Counter
from math import gcd


def remainders(a, b):
    rs = [a, b]
    while rs[-1]:
        rs.append(rs[-2] % rs[-1])
    rs.pop()
    return rs


def largest_class(rs, h, m):
    return max(Counter(r % m for r in rs[:h + 1]).values())


def main(limit=1500, width=60, control_limit=400):
    checked = failures = attained = 0
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
                    size = largest_class(rs, h, m)
                    if size == 3:
                        attained += 1
                    elif size > 3:
                        failures += 1
                        if first_failure is None:
                            first_failure = (a, b, h, m)
    print(f"instances checked: {checked}, failures: {failures}, "
          f"instances with a class of three: {attained}")
    if failures:
        raise SystemExit(f"Prefix lemma failed; first counterexample (a, b, h, m): {first_failure}")

    violations = 0
    for a in range(3, control_limit):
        for b in range(1, a):
            if gcd(a, b) != 1:
                continue
            rs = remainders(a, b)
            for h in range(1, len(rs)):
                for m in range(2, 2 * a // rs[h] + 1):
                    if largest_class(rs, h, m) > 3:
                        violations += 1
    print(f"control (hypothesis dropped, a < {control_limit}): "
          f"{violations} instances with a class of four or more")


if __name__ == "__main__":
    main(*map(int, sys.argv[1:3]))
