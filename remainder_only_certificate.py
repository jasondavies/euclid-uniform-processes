"""Offline construction and verification of remainder-only gcd derivations.

The planner is NOT a remainder-only deterministic algorithm. It uses unrestricted
Python arithmetic to choose a short derivation. Its returned certificate, however,
contains only remainder facts with operands available from the two inputs.
Only those certificate facts are counted. Independent verify() checks them.

Proved upper bound (paper, Theorem 1): O(log(max(a,b)) / log(log(max(a,b)))) certificate length.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from math import gcd
from random import Random

@dataclass
class Certificate:
    a: int
    b: int
    facts: list[tuple[int,int,int]] = field(default_factory=list)
    available: set[int] = field(default_factory=set)
    phases: int = 0
    contractions: int = 0
    max_recursion: int = 0

    def __post_init__(self) -> None:
        if self.a < 0 or self.b < 0 or self.a + self.b == 0:
            raise ValueError('Inputs must be nonnegative and not both zero')
        self.available.update((self.a, self.b))

    def emit(self, x: int, y: int) -> int:
        assert x in self.available and y in self.available and y > 0
        r = x % y
        self.facts.append((x,y,r))
        self.available.add(r)
        return r

    def plan_gcd(self, a: int, b: int, base_bits: int = 256, depth: int = 0) -> int:
        if base_bits < 64:
            raise ValueError("base_bits must be at least 64")
        self.max_recursion = max(self.max_recursion, depth)
        assert a in self.available and b in self.available
        a,b=max(a,b),min(a,b)
        if b == 0 or a == b:
            return a
        g = gcd(a,b)  # offline planning only; NOT a certificate operation
        if b == g:
            return b
        n = (a//g).bit_length()
        if n < base_bits:
            while b != g:
                a,b=b,self.emit(a,b)
            return b
        self.phases += 1
        # The paper's parameters: k = 2^p with p = floor(floor(log2 n)/2), h = 3k.
        k = 1 << ((n.bit_length()-1)//2)
        h = 3*k
        upper = g << (3*n//4)
        lower = g << ((n+2)//3)
        R=[a,b]
        while True:
            if R[-1] <= upper:
                c = R[-1]
                d = self.emit(R[-2],c)
                if d == 0:
                    assert c == g
                    return c
                return self.plan_gcd(c,d,base_bits,depth+1)
            if len(R) == h+1:
                break
            R.append(self.emit(R[-2],R[-1]))
        m=R[-1]
        assert all(x > upper for x in R)
        while m > lower:
            # Enumerating and sorting residues is unrestricted OFFLINE SEARCH.
            residue_witness = {x % m: x for x in R}
            residues = sorted(residue_witness)
            t = len(residues)
            # Euclidean-prefix lemma: each residue class holds at most three of
            # the h+1 prefix values.
            assert 3*t >= len(R) and t >= k+1, (n,h,t)
            assert (m//g)*R[-1] > 2*a
            lo,hi = min(zip(residues,residues[1:]), key=lambda z:z[1]-z[0])
            gap=hi-lo
            old_m=m
            if lo == 0:
                m=self.emit(residue_witness[hi],old_m)
            elif lo <= gap:
                m=self.emit(residue_witness[lo],old_m)
            else:
                # hi=lo+gap<2*lo, so the last remainder is exactly the gap.
                p=self.emit(residue_witness[hi],old_m)
                q=self.emit(residue_witness[lo],old_m)
                m=self.emit(p,q)
                assert m == gap
            assert 0 < m and m*(t-1) < old_m
            self.contractions += 1
        if m == g:
            return m
        u=self.emit(a,m)
        v=self.emit(b,m)
        d=self.plan_gcd(m,u,base_bits,depth+1)
        ans=self.plan_gcd(d,v,base_bits,depth+1)
        assert ans == g
        return ans

    def verify(self, output: int) -> bool:
        values={self.a,self.b}
        for i,(x,y,r) in enumerate(self.facts):
            if x not in values or y not in values or y == 0 or x % y != r:
                raise AssertionError(f'Invalid remainder fact at position {i}')
            values.add(r)
        if output not in values or output != gcd(self.a,self.b):
            raise AssertionError('Wrong or unavailable output')
        return True


def euclid_count(a: int,b: int) -> int:
    g=gcd(a,b)
    a,b=max(a,b),min(a,b)
    k=0
    while b not in (0,g):
        a,b=b,a%b
        k+=1
    return k

if __name__ == '__main__':
    import argparse,time,json
    parser=argparse.ArgumentParser()
    parser.add_argument('--bits',nargs='+',type=int,default=[512,2048,8192])
    parser.add_argument('--base-bits',type=int,default=256)
    args=parser.parse_args()
    if args.base_bits < 64 or any(n < 3 for n in args.bits):
        parser.error("base-bits must be at least 64 and all bit lengths at least 3")
    rng=Random(20261016)
    results=[]
    for n in args.bits:
        a=(1 << (n-1)) | rng.getrandbits(n-1)
        b=rng.randrange(2,a)
        while gcd(a,b)!=1:
            b=rng.randrange(2,a)
        start=time.monotonic()
        c=Certificate(a,b)
        output=c.plan_gcd(a,b,args.base_bits)
        c.verify(output)
        rec={'bits':n,'certificate_rem_calls':len(c.facts),'euclid_to_1_calls':euclid_count(a,b),
             'reservoir_phases':c.phases,'contractions':c.contractions,'max_recursion':c.max_recursion,
             'verified':True,'seconds':round(time.monotonic()-start,3)}
        results.append(rec)
        print(json.dumps(rec),flush=True)
