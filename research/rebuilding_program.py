#!/usr/bin/env python3
"""A fixed finite program that recomputes selected Euclidean-prefix values.

This tests an attempted route to one sublogarithmic program. The program is
independent of prefix length, but replays expose the extra remainder calls
needed to regenerate operands. The planner uses unrestricted arithmetic;
only the compiled program is executed by the existing independent interpreter.
No improved asymptotic bound is claimed.
"""

from __future__ import annotations

import json
from math import gcd, isqrt
from random import Random

from register_program import Function, If, Var, call, replay, validate_program


def compile_rebuilding_program() -> dict[str, Function]:
    a, b, m = Var(0), Var(1), Var(2)
    u, v = Var(0), Var(1)
    prefix = call("prefix", a, b)
    program = {
        "prefix": Function(2, (a, b, call("prefix", b, call("rem", a, b)))),
        "near": Function(2, (u, v, call("rem", u, v), call("rem", v, u))),
        "shrink": Function(3, (call("near", call("rem", prefix, m),
                                    call("rem", prefix, m)),)),
        "generate": Function(3, (m, call("generate", a, b, call("shrink", a, b, m)))),
        "loop": Function(1, (call("loop", a),)),
        "accept": Function(3, (
            If(call("eq0", m), call("loop", m),
               If(call("eq0", call("rem", a, m)),
                  If(call("eq0", call("rem", b, m)), m, call("loop", m)),
                  call("loop", m))),)),
        "gcd": Function(2, (
            If(call("eq0", b), a, call("accept", a, b, call("generate", a, b, b))),)),
    }
    validate_program(program)
    return program


def prefix_choices(index: int) -> list[tuple[str, int]]:
    if index == 0:
        return [("prefix", 0)]
    return [("prefix", 2)] * (index - 1) + [("prefix", 1)]


def witness(a: int, b: int, h: int) -> tuple[list[tuple[str, int]], dict[str, int]]:
    """Choose a convergent run; h is only an offline planning parameter."""
    if min(a, b) < 0 or h < 1:
        raise ValueError("natural inputs and a positive planning depth are required")
    if b == 0:
        return [], {"contractions": 0, "rebuilding_calls": 0, "local_calls": 0,
                    "verification_calls": 0, "expected_calls": 0}
    target = gcd(a, b)
    prefix = [a, b]
    while len(prefix) < h + 1 and prefix[-1] > 0:
        prefix.append(prefix[-2] % prefix[-1])
    choices: list[tuple[str, int]] = []
    m = b
    rebuild = local = contractions = 0
    while m != target:
        # Keep the cheapest prefix occurrence for each residue.
        indices: dict[int, int] = {}
        for i, x in enumerate(prefix):
            indices.setdefault(x % m, i)
        residues = sorted(indices)
        if len(residues) == 1:
            u = v = residues[0]
            if u == 0:
                raise AssertionError("a common divisor larger than the gcd")
            near = 0
            new_m = u
        else:
            u, v = min(zip(residues, residues[1:]), key=lambda pair: pair[1] - pair[0])
            if u == 0:
                near, new_m = 1, v
            elif u <= v - u:
                near, new_m = 0, u
            else:
                near, new_m = 3, v % u
        i, j = indices[u], indices[v]
        choices.append(("generate", 1))
        # The right residue argument is evaluated before the left one.
        choices.extend(prefix_choices(j))
        choices.extend(prefix_choices(i))
        choices.append(("near", near))
        rebuild += max(0, i - 1) + max(0, j - 1)
        local += 2 + (near >= 2)
        contractions += 1
        if not (0 < new_m < m and new_m % target == 0):
            raise AssertionError("invalid planned contraction")
        m = new_m
    choices.append(("generate", 0))
    return choices, {"contractions": contractions, "rebuilding_calls": rebuild,
                     "local_calls": local, "verification_calls": 2,
                     "expected_calls": rebuild + local + 2}


def main() -> None:
    # One compiled object is reused for every input AND every planning depth.
    program = compile_rebuilding_program()
    cases = [(a, b) for a in range(9) for b in range(9)]
    rng = Random(20261016)
    for bits in (64, 128, 512, 2048):
        a = (1 << (bits - 1)) | rng.getrandbits(bits - 1)
        b = rng.randrange(1, a)
        cases.extend(((a, b), (13*a, 13*b)))
    f, g = 1, 1
    for _ in range(300):
        f, g = g, f+g
    cases.append((g, f))
    runs = scaled = 0
    examples = []
    for a, b in cases:
        for h in (2, 5, max(2, isqrt(max(a, b).bit_length()))):
            choices, stats = witness(a, b, h)
            result = replay(program, a, b, iter(choices))
            if result.value != gcd(a, b) or result.remainder_calls != stats["expected_calls"]:
                raise AssertionError("independent replay disagrees with planner accounting")
            runs += 1
            scaled_result = replay(program, 7*a, 7*b, iter(choices))
            if (scaled_result.value != 7*result.value or
                    scaled_result.remainder_calls != result.remainder_calls):
                raise AssertionError("scaling changed a successful choice sequence")
            scaled += 1
            if a.bit_length() == 2048 and a > b:
                examples.append({"bits": a.bit_length(), "planning_h": h,
                                 "remainder_calls": result.remainder_calls, **stats})
    print(json.dumps({"program_functions": len(program), "maximum_arity": 3,
                      "runs": runs, "scaled_replays": scaled,
                      "same_program_for_all_depths": True,
                      "examples": examples}, indent=2))


if __name__ == "__main__":
    main()
