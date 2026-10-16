#!/usr/bin/env python3
"""Checks actual compiled-program executions, not just remainder-only traces."""

import json
import random
from math import gcd

from register_program import (
    Call, FuelExhausted, Function, Mod, Plan, Route, Stuck, Sub, Var,
    compile_program, replay, validate_program, witness,
)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def expect_error(error, operation):
    try:
        operation()
    except error:
        return
    raise RuntimeError(f"expected {error.__name__}")


def plan_stats(plan):
    mods = subcalls = contractions = depth = 0
    for op in plan.operations:
        if isinstance(op, Mod):
            mods += 1
            contractions += op.destination == plan.width - 3
        elif isinstance(op, Sub):
            stats = plan_stats(op.inner)
            mods += stats["generator_remainder_calls"]
            subcalls += 1 + stats["subcalls"]
            contractions += stats["contractions"]
            depth = max(depth, 1 + stats["subcall_depth"])
    return dict(generator_remainder_calls=mods, subcalls=subcalls,
                contractions=contractions, subcall_depth=depth)


def fibonacci_pair(bits):
    a, b = 1, 1
    while a.bit_length() < bits:
        a, b = a + b, a
    return a, b


def euclid_calls(a, b):
    count = 0
    while b:
        a, b = b, a % b
        count += 1
    return count


def main():
    rng = random.Random(20261016)
    cases = [(0, 0), (15, 0), (0, 15), (1, 1), (1, 37), (37, 1),
             (8, 8), (21, 14), (14, 21), (55, 89), (89, 55)]
    for bits in (40, 64, 128, 256, 512):
        for _ in range(3):
            a = rng.getrandbits(bits) | (1 << (bits - 1))
            b = rng.randrange(1, a)
            cases.extend(((a, b), (37*a, 37*b)))
    cases.extend(fibonacci_pair(bits) for bits in (64, 128, 256, 512))
    random_a = rng.getrandbits(2048) | (1 << 2047)
    random_b = rng.randrange(1, random_a)
    cases.append((random_a, random_b))
    results = []
    max_depth = 0
    total = total_subcalls = total_contractions = scaling_checks = 0
    for p in (1, 2, 3):
        width = 2 ** (2*p) + 5
        # One fixed finite program is reused for every input at this width.
        program = compile_program(width)
        for a, b in cases:
            plan = witness(a, b, p)
            run = replay(program, a, b, iter(()) if b == 0 else plan.choices())
            require(run.value == gcd(a, b), ("incorrect output", p, a, b, run))
            require(run.remainder_calls == (0 if b == 0 else plan.cost()+2),
                    ("incorrect cost", p, a, b, run, plan.cost()))
            stats = plan_stats(plan)
            require(stats["generator_remainder_calls"] == plan.cost(), "plan accounting mismatch")
            total += 1
            total_subcalls += stats["subcalls"]
            total_contractions += stats["contractions"]
            max_depth = max(max_depth, stats["subcall_depth"])
            if a > 0 and b > 0:
                scaled = replay(program, 13*a, 13*b, plan.choices())
                require(scaled.value == 13*gcd(a, b), "scaled output mismatch")
                require(scaled.remainder_calls == run.remainder_calls,
                        "scaling changed remainder cost")
                scaling_checks += 1
        for name, (a, b) in (("fibonacci", fibonacci_pair(512)),
                              ("seeded_random", (random_a, random_b))):
            plan = witness(a, b, p)
            run = replay(program, a, b, plan.choices())
            results.append(dict(family=name, p=p, registers=width,
                                input_bits=a.bit_length(),
                                remainder_calls=run.remainder_calls,
                                euclid_calls=euclid_calls(a, b),
                                internal_calls=run.internal_calls,
                                nondeterministic_choices=run.choice_count,
                                **plan_stats(plan)))

    require(total_subcalls > 0, "recursive subcomputations were not exercised")
    require(total_contractions > 0, "reservoir contractions were not exercised")
    require(max_depth >= 2, "nested recursive subcomputations were not exercised")
    x, y = 89, 55
    ops = []
    while y:
        ops.extend((Mod(0, 0, 1), Route((1, 0))))
        x, y = y, x % y
    minimal = Plan(2, ops, 0)
    small_run = replay(compile_program(2), 89, 55, minimal.choices())
    require(small_run.value == 1 and small_run.remainder_calls == minimal.cost()+2,
            "two-register Euclid failed")
    program = compile_program(9)
    # A candidate that is a multiple of the gcd but not a common divisor is rejected.
    expect_error(FuelExhausted, lambda: replay(program, 15, 6,
                 Plan(9, [], 0).choices(), fuel=1000))
    # A generated zero must not pass verification.
    expect_error(FuelExhausted, lambda: replay(program, 15, 6,
                 Plan(9, [Mod(0, 0, 0)], 0).choices(), fuel=1000))
    # Partial remainder is genuinely undefined at a zero divisor.
    expect_error(Stuck, lambda: replay(program, 0, 7,
                 Plan(9, [Mod(0, 1, 0)], 0).choices()))
    expect_error(ValueError, lambda: replay(program, 15, 6, iter(())))
    expect_error(ValueError, lambda: replay(program, 15, 6, iter([("choose", 0)])))
    for bad in (Function(2, (Var(2),)),
                Function(2, (Call("gcd_oracle", (Var(0), Var(1))),)),
                Function(2, (7,))):
        invalid = dict(program, gcd=bad)
        expect_error(ValueError, lambda: validate_program(invalid))
    print(json.dumps(dict(
        successful_cases=total,
        same_choices_scaling_checks=scaling_checks,
        recursive_subcomputations=total_subcalls,
        reservoir_contractions=total_contractions,
        maximum_subcall_depth=max_depth,
        two_register_euclid_check=True,
        rejection_checks=8,
        examples=results,
        scope="finite compiled programs; offline witnesses; no sublogarithmic program claim",
    ), indent=2))


if __name__ == "__main__":
    main()
