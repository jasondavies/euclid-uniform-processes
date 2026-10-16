"""Reproduce finite checks; no timing or planner arithmetic is counted as a proof."""
import json
from math import gcd
from pathlib import Path
from random import Random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from remainder_only_certificate import Certificate

rng = Random(20261016)
cases = [(a, b) for a in range(12) for b in range(12) if a or b]
for i in range(100):
    bits = [64, 128, 256, 512, 1024][i % 5]
    a = (1 << (bits - 1)) | rng.getrandbits(bits - 1)
    b = rng.randrange(1, a)
    scale = [1, 2, 17, 65537][i % 4]
    cases.append((scale * a, scale * b))
f0, f1 = 0, 1
fib = [0, 1]
for _ in range(3200):
    f0, f1 = f1, f0 + f1
    fib.append(f1)
for i in range(60):
    k = 3 + 53*i
    scale = 1 if i % 2 else 35
    cases.append((scale*fib[k+1], scale*fib[k]))
cases.extend([(1, 1), (1 << 4096, 0), (0, 1 << 4096),
              (1 << 4096, 1), (1 << 4096, 1 << 4096),
              (1 << 4096, (1 << 4096)-1), (17 << 1024, 17 << 512)])
assert len(cases) == 310
contractions = phases = 0
for a, b in cases:
    cert = Certificate(a, b)
    output = cert.plan_gcd(a, b, base_bits=64)
    assert cert.verify(output)
    phases += cert.phases
    contractions += cert.contractions

# Deliberately invalid traces must be rejected by the separate replay checker.
invalid = [([(13, 5, 3)], 1),          # unavailable operand
           ([(13, 0, 0)], 1),          # zero divisor
           ([(13, 8, 4)], 1),          # false remainder equation
           ([], 1)]                    # unavailable output
for facts, output in invalid:
    cert = Certificate(13, 8)
    cert.facts = facts
    try:
        cert.verify(output)
    except AssertionError:
        pass
    else:
        raise AssertionError('Replay checker accepted an invalid trace')
print(json.dumps({'verified_cases': len(cases),
                  'noncoprime_cases': sum(gcd(a, b) != 1 for a, b in cases),
                  'reservoir_phases': phases,
                  'contractions': contractions,
                  'invalid_traces_rejected': len(invalid),
                  'seed': 20261016, 'base_bits': 64}, indent=2))
