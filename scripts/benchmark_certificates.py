"""Reproduce the paper's illustrative distribution of remainder-call counts.

The planner uses unrestricted arithmetic. Only the resulting derivation's
remainder calls are counted, and Certificate.verify independently replays each
derivation. These finite samples do not establish an asymptotic or average-case
bound. Run from the repository root, for example:

    python3 scripts/benchmark_certificates.py > validation/benchmark_certificates.json
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from math import gcd
from pathlib import Path
from random import Random
from statistics import median
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from remainder_only_certificate import Certificate, euclid_count


def input_digest(a: int, b: int) -> str:
    """Identify a pair without storing thousands of decimal digits."""
    return sha256(f"{a:x}:{b:x}".encode("ascii")).hexdigest()


def measure(a: int, b: int, base_bits: int) -> dict:
    certificate = Certificate(a, b)
    output = certificate.plan_gcd(a, b, base_bits=base_bits)
    certificate.verify(output)
    return {
        "inputs_sha256": input_digest(a, b),
        "a_bits": a.bit_length(),
        "b_bits": b.bit_length(),
        "construction_calls": len(certificate.facts),
        "euclid_to_gcd_calls": euclid_count(a, b),
        "prefix_phases": certificate.phases,
        "contractions": certificate.contractions,
        "max_recursion": certificate.max_recursion,
        "verified": True,
    }


def summarize(records: list[dict], key: str) -> dict:
    values = [record[key] for record in records]
    return {"min": min(values), "median": median(values), "max": max(values)}


def fibonacci_pair(bits: int) -> tuple[int, int, int]:
    """Return (F_k, F_{k-1}, k), taking the smallest k with bits(F_k)=bits."""
    previous, current, index = 0, 1, 1
    while current.bit_length() < bits:
        previous, current = current, previous + current
        index += 1
    assert current.bit_length() == bits
    return current, previous, index


def worked_contraction() -> dict:
    certificate = Certificate(44, 17)
    modulus = certificate.emit(44, 17)
    prefix = [44, 17, modulus]
    residues = sorted({value % modulus for value in prefix})
    # The prefix lemma applies, and the selected residues 4, 7 are adjacent.
    assert modulus * prefix[-1] > 2 * prefix[0]
    assert residues == [0, 4, 7]
    high = certificate.emit(17, modulus)
    low = certificate.emit(44, modulus)
    contracted = certificate.emit(high, low)
    assert 0 < contracted * (len(residues) - 1) < modulus
    output = certificate.emit(modulus, contracted)
    certificate.verify(output)
    return {
        "inputs": [44, 17],
        "prefix": prefix,
        "modulus": modulus,
        "distinct_residues": residues,
        "selected_residues": [low, high],
        "contraction_facts": certificate.facts[1:4],
        "new_modulus": contracted,
        "full_derivation": certificate.facts,
        "output": output,
        "verified": True,
        "purpose": "Illustrates the three-call contraction; no speedup is claimed for this pair.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bits", nargs="+", type=int, default=[512, 2048, 8192])
    parser.add_argument("--samples", type=int, default=25)
    parser.add_argument("--seed", type=int, default=20261016)
    parser.add_argument("--base-bits", type=int, default=256)
    args = parser.parse_args()
    if args.samples < 1 or args.base_bits < 64 or any(bits < 3 for bits in args.bits):
        parser.error("samples must be positive, base-bits at least 64, and bit lengths at least 3")

    rng = Random(args.seed)
    groups = []
    for bits in args.bits:
        records = []
        for sample in range(1, args.samples + 1):
            a = (1 << (bits - 1)) | rng.getrandbits(bits - 1)
            b = rng.randrange(2, a)
            while gcd(a, b) != 1:
                b = rng.randrange(2, a)
            records.append({"sample": sample, **measure(a, b, args.base_bits)})
        a, b, index = fibonacci_pair(bits)
        groups.append({
            "bits": bits,
            "random_summary": {
                "samples": len(records),
                "construction_calls": summarize(records, "construction_calls"),
                "euclid_to_gcd_calls": summarize(records, "euclid_to_gcd_calls"),
            },
            "random_samples": records,
            "fibonacci": {"larger_fibonacci_index": index, **measure(a, b, args.base_bits)},
        })

    result = {
        "seed": args.seed,
        "base_bits": args.base_bits,
        "bit_lengths_in_generation_order": args.bits,
        "samples_per_bit_length": args.samples,
        "random_sampling": (
            "One Python Random(seed) stream, in the listed bit-length order. "
            "For each sample, a is uniform among integers of exactly the specified bit length; "
            "b is drawn uniformly from [2,a-1] until gcd(a,b)=1, keeping a fixed. "
            "This is not uniform sampling over all coprime pairs in the range."
        ),
        "fibonacci_selection": (
            "F_0=0, F_1=1; take (F_k,F_{k-1}) for the smallest k with F_k of the specified bit length."
        ),
        "inputs_sha256_encoding": "ASCII lowercase hexadecimal a, colon, lowercase hexadecimal b; no prefixes or newline.",
        "cost_convention": (
            "Count every remainder call in the returned derivation, including repetitions. "
            "The Euclidean baseline stops when the gcd first becomes available, "
            "without a final zero-producing call. All inputs here are coprime, so the target is 1. "
            "Planner arithmetic and elapsed time are not measured."
        ),
        "groups": groups,
        "worked_contraction": worked_contraction(),
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
