#!/usr/bin/env python3
"""Compile and replay a finite first-order nondeterministic remainder program.

The program AST has variables, calls and conditionals, with only rem and eq0
as primitives. No lists, indices, constants, comparisons or gcd are data
operations of the compiled program. Python arithmetic in witness() selects
one successful nondeterministic branch offline; it is not a program primitive.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from math import gcd
from typing import Iterator


@dataclass(frozen=True)
class Var:
    index: int


@dataclass(frozen=True)
class Call:
    name: str
    args: tuple[Expr, ...]


@dataclass(frozen=True)
class If:
    condition: Expr
    yes: Expr
    no: Expr


Expr = Var | Call | If


@dataclass(frozen=True)
class Function:
    arity: int
    alternatives: tuple[Expr, ...]


def call(name: str, *args: Expr) -> Call:
    return Call(name, args)


def compile_program(width: int) -> dict[str, Function]:
    """Width is a compile-time parameter, fixed independently of input values."""
    if width < 2:
        raise ValueError("at least two registers are required")
    xs = tuple(Var(i) for i in range(width))
    pick = Call("choose", xs)
    alternatives: list[Expr] = [pick]
    alternatives += [
        call(f"set_{i}", *xs, call("rem", pick, pick)) for i in range(width)
    ]
    alternatives += [
        call(f"set_{i}", *xs, Call("gen", xs)) for i in range(width)
    ]
    alternatives.append(Call("gen", (pick,) * width))
    program = {
        "choose": Function(width, xs),
        "gen": Function(width, tuple(alternatives)),
        "loop": Function(1, (call("loop", Var(0)),)),
    }
    for i in range(width):
        args = tuple(Var(width) if j == i else Var(j) for j in range(width))
        program[f"set_{i}"] = Function(width + 1, (Call("gen", args),))
    a, b, g = Var(0), Var(1), Var(2)
    program["accept"] = Function(3, (
        If(call("eq0", g), call("loop", g),
           If(call("eq0", call("rem", a, g)),
              If(call("eq0", call("rem", b, g)), g, call("loop", g)),
              call("loop", g))),
    ))
    initial = tuple(b if i == 1 else a for i in range(width))
    program["gcd"] = Function(2, (
        If(call("eq0", b), a, call("accept", a, b, Call("gen", initial))),
    ))
    validate_program(program)
    return program


def validate_program(program: dict[str, Function]) -> None:
    """Type/arity check the actual finite syntax, rejecting extra primitives."""
    def infer(expr: Expr, arity: int) -> str:
        if isinstance(expr, Var):
            if not 0 <= expr.index < arity:
                raise ValueError("variable outside its fixed argument tuple")
            return "nat"
        if isinstance(expr, If):
            if infer(expr.condition, arity) != "bool":
                raise ValueError("nonboolean guard")
            left, right = infer(expr.yes, arity), infer(expr.no, arity)
            if left != right:
                raise ValueError("branch sort mismatch")
            return left
        if not isinstance(expr, Call):
            raise ValueError("unsupported syntax (including numeric constants)")
        expected = {"rem": 2, "eq0": 1}
        if expr.name in program:
            expected_arity = program[expr.name].arity
        elif expr.name in expected:
            expected_arity = expected[expr.name]
        else:
            raise ValueError(f"unknown function: {expr.name}")
        if len(expr.args) != expected_arity:
            raise ValueError("arity mismatch")
        if any(infer(arg, arity) != "nat" for arg in expr.args):
            raise ValueError("nonnatural argument")
        return "bool" if expr.name == "eq0" else "nat"

    if "rem" in program or "eq0" in program:
        raise ValueError("primitive redefinition")
    for function in program.values():
        if not function.alternatives:
            raise ValueError("empty definition")
        for body in function.alternatives:
            if infer(body, function.arity) != "nat":
                raise ValueError("unexpected function result sort")


class Stuck(Exception):
    """An undefined remainder call cannot produce a convergent computation."""


class FuelExhausted(Exception):
    """A finite replay budget was exhausted; this does not prove divergence."""


@dataclass(frozen=True)
class Replay:
    value: int
    remainder_calls: int
    zero_tests: int
    internal_calls: int
    choice_count: int
    max_pending: int


def replay(program: dict[str, Function], a: int, b: int,
           choices: Iterator[tuple[str, int]], fuel: int = 20_000_000) -> Replay:
    """Call-by-value interpreter, evaluating arguments right to left as in §2D.

    Stack frames hold syntax and environments of statically fixed arity.
    Evaluated natural values are never used as host-language addresses.
    """
    if type(a) is not int or type(b) is not int or a < 0 or b < 0:
        raise ValueError("inputs must be natural numbers")
    pending = [("eval", call("gcd", Var(0), Var(1)), (a, b))]
    values: list[int | bool] = []
    rem_calls = zero_tests = internal_calls = choice_count = 0
    max_pending = 1
    for _ in range(fuel):
        if not pending:
            if len(values) != 1 or type(values[0]) is not int:
                raise ValueError("malformed terminal configuration")
            try:
                next(choices)
            except StopIteration:
                return Replay(values[0], rem_calls, zero_tests, internal_calls,
                              choice_count, max_pending)
            raise ValueError("unused nondeterministic choices")
        max_pending = max(max_pending, len(pending))
        task = pending.pop()
        if task[0] == "eval":
            _, expr, env = task
            if isinstance(expr, Var):
                values.append(env[expr.index])
            elif isinstance(expr, If):
                pending.append(("branch", expr.yes, expr.no, env))
                pending.append(("eval", expr.condition, env))
            elif isinstance(expr, Call):
                pending.append(("apply", expr.name, len(expr.args)))
                pending.extend(("eval", arg, env) for arg in expr.args)
            else:
                raise ValueError("unknown syntax")
        elif task[0] == "branch":
            condition = values.pop()
            if type(condition) is not bool:
                raise ValueError("nonboolean branch value")
            pending.append(("eval", task[1] if condition else task[2], task[3]))
        elif task[0] == "apply":
            _, name, arity = task
            args = tuple(values.pop() for _ in range(arity))
            if any(type(x) is not int for x in args):
                raise ValueError("nonnatural function argument")
            if name == "rem":
                if args[1] == 0:
                    raise Stuck("undefined remainder with zero divisor")
                values.append(args[0] % args[1])
                rem_calls += 1
            elif name == "eq0":
                values.append(args[0] == 0)
                zero_tests += 1
            else:
                internal_calls += 1
                function = program[name]
                if len(function.alternatives) == 1:
                    index = 0
                else:
                    try:
                        choice_name, index = next(choices)
                    except StopIteration as exc:
                        raise ValueError("missing nondeterministic choice") from exc
                    if choice_name != name or not 0 <= index < len(function.alternatives):
                        raise ValueError("invalid nondeterministic choice")
                    choice_count += 1
                pending.append(("eval", function.alternatives[index], args))
        else:
            raise ValueError("unknown interpreter task")
    raise FuelExhausted("replay budget exhausted")


@dataclass(frozen=True)
class Mod:
    destination: int
    left: int
    right: int


@dataclass(frozen=True)
class Route:
    sources: tuple[int, ...]


@dataclass(frozen=True)
class Sub:
    destination: int
    inner: Plan


@dataclass
class Plan:
    width: int
    operations: list[Mod | Route | Sub]
    result: int

    def cost(self) -> int:
        return sum(1 if isinstance(op, Mod) else op.inner.cost()
                   if isinstance(op, Sub) else 0 for op in self.operations)

    def choices(self) -> Iterator[tuple[str, int]]:
        for op in self.operations:
            if isinstance(op, Mod):
                yield "gen", 1 + op.destination
                yield "choose", op.right
                yield "choose", op.left
            elif isinstance(op, Route):
                yield "gen", 2 * self.width + 1
                for source in reversed(op.sources):
                    yield "choose", source
            else:
                yield "gen", 1 + self.width + op.destination
                yield from op.inner.choices()
        yield "gen", 0
        yield "choose", self.result


def seed(width: int, left: int, right: int) -> tuple[int, ...]:
    return tuple(right if i == 1 else left for i in range(width))


def witness(a: int, b: int, p: int, base_bits: int = 32) -> Plan:
    """Offline witness for a fixed-width program; p is NOT a runtime input.

    The illustrative planner uses thresholds 3n/4 and n/3. The mathematical
    family bound also considers other thresholds, all within the same program.
    """
    if p < 1 or base_bits < 16:
        raise ValueError("require p >= 1 and base_bits >= 16")
    h = 2 ** (2 * p) + 1
    width = h + 4
    if b == 0:
        return Plan(width, [], 0)
    common = gcd(a, b)
    a, b = a // common, b // common
    if a < b:
        child = witness(b, a, p, base_bits)
        return Plan(width, [Route(seed(width, 1, 0))] + child.operations, child.result)
    regs = [b if i == 1 else a for i in range(width)]
    ops: list[Mod | Route | Sub] = []

    def mod(dest: int, left: int, right: int) -> None:
        if regs[right] == 0:
            raise ValueError("planner attempted undefined remainder")
        ops.append(Mod(dest, left, right))
        regs[dest] = regs[left] % regs[right]

    def route(sources: tuple[int, ...]) -> None:
        ops.append(Route(sources))
        regs[:] = [regs[i] for i in sources]

    def finish(left: int, right: int) -> Plan:
        child = witness(regs[left], regs[right], p, base_bits)
        route(seed(width, left, right))
        return Plan(width, ops + child.operations, child.result)

    n = (a - 1).bit_length()
    if n <= base_bits:
        while regs[1]:
            mod(2, 0, 1)
            route(seed(width, 1, 2))
        return Plan(width, ops, 0)
    early = 2 ** ((3 * n + 3) // 4)
    small = 2 ** ((n + 2) // 3)
    mslot, uslot, vslot = h + 1, h + 2, h + 3
    last = 1
    while True:
        if regs[last] == 0:
            return Plan(width, ops, last - 1)
        if regs[last] <= early:
            mod(uslot, last - 1, last)
            return finish(last, uslot)
        if last == h:
            break
        mod(last + 1, last - 1, last)
        last += 1
    sources = list(range(width))
    sources[mslot] = h
    route(tuple(sources))
    while regs[mslot] > small:
        old = regs[mslot]
        representatives: dict[int, int] = {}
        for i in range(h + 1):
            representatives.setdefault(regs[i] % old, i)
        residues = sorted(representatives)
        if len(residues) < 2:
            raise ValueError("prefix did not supply distinct residues")
        u, v = min(zip(residues, residues[1:]), key=lambda uv: uv[1] - uv[0])
        if u == 0:
            mod(mslot, representatives[v], mslot)
        elif u <= v - u:
            mod(mslot, representatives[u], mslot)
        else:
            mod(vslot, representatives[v], mslot)
            mod(uslot, representatives[u], mslot)
            mod(mslot, vslot, uslot)
        if not 0 < regs[mslot] * 2**p < old:
            raise ValueError("contraction did not meet the proved factor")
    mod(uslot, 0, mslot)
    mod(vslot, 1, mslot)
    inner = witness(regs[mslot], regs[uslot], p, base_bits)
    inner = Plan(width, [Route(seed(width, mslot, uslot))] + inner.operations,
                 inner.result)
    ops.append(Sub(mslot, inner))
    regs[mslot] = gcd(regs[mslot], regs[uslot])
    return finish(mslot, vslot)


def render(program: dict[str, Function]) -> str:
    def expr_text(expr: Expr) -> str:
        if isinstance(expr, Var):
            return f"x{expr.index}"
        if isinstance(expr, If):
            return (f"if {expr_text(expr.condition)} then {expr_text(expr.yes)} "
                    f"else {expr_text(expr.no)}")
        return f"{expr.name}(" + ", ".join(map(expr_text, expr.args)) + ")"

    lines = []
    for name, function in program.items():
        parameters = ", ".join(f"x{i}" for i in range(function.arity))
        for body in function.alternatives:
            lines.append(f"{name}({parameters}) = {expr_text(body)}")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--width", type=int, default=9)
    args = parser.parse_args()
    print(render(compile_program(args.width)), end="")
