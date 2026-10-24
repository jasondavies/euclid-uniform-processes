module

public import ShortGCD.RegisterRecursion
public import ShortGCD.TailSource

@[expose] public section

/-! # The register program as a tail-recursive program

The register program of `TailSource`, compiled by `Register.compile` into a finite
nondeterministic recursive program in the sense of Moschovakis's book (§§2A, 2E): one
function symbol per line, each taking the `w + 2` registers, as in the book's reduction of
iteration to tail recursion (§2C). The head calls the symbol of line `0` with the registers
initialised to `(a, b, a, b, a, …, a)`.

`executes_iff_eval` matches evaluations of the head exactly, with the same value and remainder
cost, with executions of the register program, and `executes_iff_steps` transfers this to the
Lean model of the book's recursive machine (`Recursive.Machine`, a specialisation of its
Table 1). `program_tailRecursive` certifies syntactically that every call is a tail call, and
`stacks_bounded` bounds the machine's stacks independently of the input.
-/

namespace ShortGCD.TailRecursive
open TailProgram Register Recursive

/-- The function symbols: the numbered lines of the register program. -/
abbrev Sym (w : ℕ) := Fin ((TailSource.program w).L+1)

/-- The bodies of each line symbol. -/
noncomputable def bodies (w : ℕ) := compile (TailSource.program w).line

/-- Register `x` starts with input `1` (that is, `b`) if `x` is `1` or `3`, and with input
`0` (`a`) otherwise. -/
def initVar (w : ℕ) : Fin (2+w) → Fin 2 := fun x => if x.val = 1 ∨ x.val = 3 then 1 else 0

/-- The head: call line `0` with the initial registers. -/
noncomputable def head (w : ℕ) : RExpr (2+w) (Sym w) 2 := Register.head 0 (initVar w)

lemma init_eq (w a b : ℕ) : ![a,b] ∘ initVar w = TailSource.init w a b := by
  funext x
  simp only [Function.comp, initVar, TailSource.init]
  split_ifs <;> rfl

/-- The compiled program is finite: finitely many symbols, each with finitely many bodies. -/
theorem bodies_finite (w : ℕ) (f : Sym w) : (bodies w f).Finite :=
  compile_finite _ f

/-- Syntactic certification of tail recursion for the complete program. -/
theorem program_tailRecursive (w : ℕ) : Recursive.IsTailRecursive (bodies w) (head w) :=
  compile_tailRecursive _ 0 (initVar w)

/-- Executions of the register program and evaluations of the recursive program correspond
exactly, with the same value and remainder cost. -/
theorem executes_iff_eval (w a b c z : ℕ) :
    TailSource.Executes w a b c z ↔ Eval (bodies w) ![a,b] (head w) c z := by
  rw [bodies, head, eval_iff_halts, init_eq]
  rfl

/-- The initial machine state evaluating the head on `a, b`, and the halting state. -/
noncomputable def start (w a b : ℕ) : Machine.State (arity (2+w) (Sym w)) :=
  ⟨[.eval (.mk ![a,b] (head w))], []⟩
def halt (w z : ℕ) : Machine.State (arity (2+w) (Sym w)) := ⟨[], [.nat z]⟩

/-- The same correspondence for the Lean model of the book's recursive machine. -/
theorem executes_iff_steps (w a b c z : ℕ) :
    TailSource.Executes w a b c z ↔ Machine.Steps (bodies w) (start w a b) c (halt w z) :=
  (executes_iff_eval w a b c z).trans Machine.eval_iff_steps

/-- Every halting machine computation returns the gcd. -/
theorem steps_correct {w a b c z} (h : Machine.Steps (bodies w) (start w a b) c (halt w z)) :
    z = Nat.gcd a b :=
  TailSource.executes_correct ((executes_iff_steps w a b c z).mpr h)

/-- Every input has a halting machine computation. -/
theorem steps_total {w} (hw : 2 ≤ w) (a b : ℕ) :
    ∃ c, Machine.Steps (bodies w) (start w a b) c (halt w (Nat.gcd a b)) := by
  obtain ⟨c, hc⟩ := TailSource.executes_total hw a b
  exact ⟨c, (executes_iff_steps w a b c _).mp hc⟩

/-- **No recursion stack.** Every state reachable by the machine model from the head has at
most `2w + 8` entries on its control and value stacks together, independently of the inputs
and of the length of the computation. Each closure environment holds the `w + 2` registers,
or the two inputs for the head and its arguments. -/
theorem stacks_bounded {w a b k} {t : Machine.State (arity (2+w) (Sym w))}
    (h : Machine.Steps (bodies w) (start w a b) k t) :
    t.control.length + t.values.length ≤ 2*w+8 := by
  have := Register.stacks_bounded _ 0 (initVar w) h
  omega

/-- **Arbitrarily small coefficients for recursive programs**: for every `ε > 0` there are
`p > 0` and `B ≥ 0` such that, for all `1 ≤ b ≤ a`, the machine model running the
fixed tail-recursive program for width `4^p + 5` halts with output `gcd(a, b)` at remainder
cost at most `ε log₂ a + B`. -/
theorem arbitrarily_small_coefficient {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℕ, 0 < p ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℕ, 1 ≤ b → b ≤ a →
      ∃ c, Machine.Steps (bodies (Fixed.width p)) (start (Fixed.width p) a b) c
          (halt (Fixed.width p) (Nat.gcd a b)) ∧
        (c:ℝ) ≤ ε*Real.logb 2 a+B := by
  obtain ⟨p, hp, B, hB, h⟩ := TailSource.arbitrarily_small_coefficient hε
  refine ⟨p, hp, B, hB, fun a b hb hab => ?_⟩
  obtain ⟨c, hc, hbound⟩ := h a b hb hab
  exact ⟨c, (executes_iff_steps _ a b c _).mp hc, hbound⟩

end ShortGCD.TailRecursive
