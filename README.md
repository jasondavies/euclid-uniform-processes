# The Euclidean algorithm is not optimal among uniform processes

Logarithmic remainder-call lower bounds for gcd and coprimeness cannot follow from
uniformity alone. Every pair a ≥ b has a remainder-only derivation of gcd(a, b) using
O(log a / log log a) remainder calls. Each call takes the remainder of two values
already available, starting from a and b; earlier values are kept and no numerical
constants are introduced. Euclid needs about 1.44 log₂ a calls in the worst case
(successive Fibonacci numbers).

The refined upper bound is **(6 + o(1)) log₂ a / log₂ log₂ a**, uniformly in b.
Precisely, for every ε > 0, the coefficient 6 + ε works for all sufficiently large a
and every 0 ≤ b ≤ a. The same leading coefficient holds for the intrinsic
remainder-call complexities below on positive inputs. No optimality of 6 is claimed.

As a consequence, the intrinsic calls(rem)-complexity of both coprimeness and gcd in
the Euclidean structure Nε = (N, rem, eq0, eq1) is o(log a), uniformly over pairs with
1 ≤ b ≤ a. This refutes the uniform-process form of van den Dries and Moschovakis's
conjecture that the Euclidean algorithm is optimal among its peers:

- **Conjecture 3.4** of Moschovakis's 2012 notes, *Absolute lower bounds for uniform
  processes*: there is no r > 0 with calls(rem)(Nε, ⊥⊥, a, b) ≥ r log a for infinitely
  many a ≥ b ≥ 1. In Lean this is `ShortGCD.not_conjecture_3_4`, and
  `ShortGCD.not_conjecture_3_4_literal` for the exact wording (rational r, infinitely many a).
- **The "precise version" (4F-5) of the Main Conjecture** in *Abstract Recursion and
  Intrinsic Complexity* (2019, p. 151): there is no K > 0 with
  2 log max(x, y) ≤ K · calls(rem)(gcd, x, y) on infinitely many pairs. In Lean this is
  `ShortGCD.not_main_conjecture_4F5`, for gcd certificates without eq1 facts, and
  `ShortGCD.not_main_conjecture_4F5_Neps`, for certificates in Nε.
  `ShortGCD.not_main_conjecture_4F5_literal` refutes the book's form, with a set D on which
  the complexity is unbounded (condition (4F-4)). It drops the book's first inequality,
  calls(rem)(ε, x, y) ≤ L(x, y), which only makes the refuted statement weaker.
- **The possibility raised after Corollary 6C.7 (p. 188)**, that the Main Conjecture
  "holds for all uniform processes of Nε". Ruling this out also uses the book's
  best-uniform-process theorem (4F.1), which turns a small intrinsic complexity into a
  uniform process with that complexity. Theorem 4F.1 is cited, not formalised.

**The Main Conjecture for algorithms remains open.** The construction gives no
remainder-only algorithm, deterministic or nondeterministic, with this cost: choosing which
two stored residues to combine is not charged. The book's best-uniform-process theorem
(4F.1) supplies a uniform process attaining the bound. The result shows that a proof of
the Main Conjecture must use properties beyond uniformity. The Homomorphism Test applied to all generated primitive
operation diagrams cannot prove a logarithmic lower bound: every input has a certificate
with o(log a) remainder facts. This leaves open arguments combining homomorphisms with
additional restrictions on computations. A nondeterministic program would still need
to implement reusable access to the growing stored prefix within the claimed cost.

**A further algorithmic result:** for every ε > 0, there is a fixed finite
nondeterministic recursive gcd program using only rem and eq0 with cost at most
ε log₂ a + Bε on all positive inputs a ≥ b. Cost is the minimum number of remainder
calls over successful computations; every terminating computation is correct.
The program depends on ε. This family does not give one sublogarithmic program.
The theorem and proof are included in Section 6 of the paper and checked in Lean.

Read `paper/euclid-uniform-processes.pdf`, built from `paper/euclid-uniform-processes.tex`.
Page citations refer to the published edition of Moschovakis, *Abstract Recursion and
Intrinsic Complexity* (Lecture Notes in Logic 48, Cambridge University Press / ASL, 2019,
doi:10.1017/9781108234238).

**Status.** The upper bounds, including the leading coefficient 6, the finite
nondeterministic program-family bound, and the refutations of Conjecture 3.4 and
(4F-5) are machine-checked in Lean, as listed below. The consequence
for the question on p. 188 also uses the cited Theorem 4F.1. A second, independent Lean
formalisation of the original Big-O argument was developed separately. The result has
not yet been reviewed by an expert in the area.

## Lean verification

The project pins Lean and mathlib to v4.35.0. On a fresh checkout with elan:

```
lake exe cache get
lake build
lake env lean validation/Axioms.lean
```

### Main results

The conjectures:

- `ShortGCD.not_conjecture_3_4`, `ShortGCD.not_main_conjecture_4F5` and
  `ShortGCD.not_main_conjecture_4F5_Neps` state the refutations above. The (4F-5)
  statements cover all pairs in ℕ², including pairs with a zero entry, which need no
  remainder facts (`callsGcd_zero_left`, `callsGcd_zero_right`).
- **The definitions.** The intrinsic complexities `callsCoprimeness`, `callsGcd` and
  `callsRemGcd` are defined directly from certificates. A certificate is a finite partial
  substructure generated by the input, such that every map preserving its facts respects
  the relation or function. Coprimeness is the book's relation `BookCoprime`: x, y ≥ 1 and
  gcd(x, y) = 1.
- `ShortGCD.eventually_calls_le`: for every ε > 0, eventually in M, `callsCoprimeness`
  and `callsGcd` are at most ε log₂ M on all pairs with 0 < a, b ≤ M.
- `ShortGCD.callsRem_eq_D` (the reduction): on coprime pairs, the least number of
  remainder facts in a certificate for `Nat.Coprime` equals D(a, b), the length of a
  shortest remainder derivation of 1. The doubling map u ↦ 2u shows that every
  certificate must reach 1.
- `ShortGCD.certifiesCoprimeness_of_certifiesCoprime` and
  `ShortGCD.callsCoprimeness_eq_callsRem`: adding the facts eq0(a) = ff and eq0(b) = ff
  turns a `Nat.Coprime` certificate into one for the book's relation, with the same
  remainder facts. So for positive coprime inputs the two complexities agree.
- `ShortGCD.callsRemGcd_le_callsGcd`: allowing eq1 facts can only lower the gcd
  complexity.

Derivations and certificates:

- `ShortGCD.uniform_real_bound_six`: for every ε > 0, eventually in a, the coefficient
  6 + ε bounds G(a, b) / (log₂ a / log₂ log₂ a) for every b ≤ a.
- `ShortGCD.uniform_intrinsic_bound_six`: the same statement for `callsCoprimeness`,
  `callsGcd` and `callsRemGcd`, for every positive b ≤ a.
- `ShortGCD.Sharp.limsup_profile_le_six`: the upper limit of
  sizeCost(2ⁿ) · log₂ n / n is at most 6. `eventually_sizeCost_add_le_six` also absorbs
  any fixed additive instruction overhead.
- `ShortGCD.uniform_real_bound`: one real constant bounds G(a, b), for every a ≥ 4 and
  b ≤ a, by C · logb 2 a / logb 2 (logb 2 a).
- `ShortGCD.sizeCost_isBigO` and `ShortGCD.sizeCost_isLittleO_log`: worst-case Big-O and
  little-o statements, taking the maximum over all smaller inputs.
- `ShortGCD.uniform_gcd_certificates`: generated gcd certificates with at most the same
  bound plus two remainder facts, and no eq1 facts.
- `ShortGCD.callsCoprimeness_le`: for a, b ≥ 1, the book's coprimeness relation has a
  certificate with at most G(a, b) + 2 remainder facts, for either truth value. It is built
  from `coprime_certificate_bound` (true instances of `Nat.Coprime`, at most G(a, b)) and
  `noncoprime_certificate_bound` (false instances, a > 0, at most G(a, b) + 2).
- `ShortGCD.G_eq_D`: G agrees with D, the list-derivation definition, on coprime inputs.
- `ShortGCD.gcd_certificate_lower`: every generated gcd certificate has at least G(a, b)
  remainder facts.
- `ShortGCD.AlmostAll.card_within_le`: at most 40 (2 + ln N) N^(2 − 2^(−d)) pairs
  2 ≤ b < a ≤ N have a derivation of 1 of length at most d. Hence
  `ShortGCD.AlmostAll.tendsto_card_within_loglog`: D(a, b) > (1 − ε) log₂ log₂ N for all
  but o(N²) pairs, so the Ω(log log a) lower bound holds on almost all pairs, not only on
  the book's difficult pairs.

### Proof path

- **Certificates and the reduction:** CoprimeCertificate → RemainderList →
  GcdCertificate.
- **The upper bound:** Derivation → Composition → Normalization, and Derivation → Gap;
  Prefix stands alone. Gap, Composition and Prefix feed Contraction. Contraction and
  Normalization feed Euclid → FiniteBound. FiniteBound and Arithmetic feed UpperBound →
  Asymptotic → SharpBound.
- **Both strands meet** in Certificates → Conjecture; SharpCertificates combines the
  refined bound with the certificate reductions.

- **The finite recurrence.** The core is `sizeCost_step`. Its hypotheses concern
  natural-number size parameters, not an assumed complexity bound.
- **The bound.** Arithmetic discharges those hypotheses, and UpperBound proves the
  resulting bound by strong induction.
- **The logarithms.** Asymptotic compares integer logarithms with real logarithms.
- **The leading coefficient.** SharpBound reuses `sizeCost_step` with tunable prefix
  and recursive-size parameters. The original Big-O theorem supplies boundedness;
  an upper-limit argument gives 6, and rounding limits preserve it for general inputs.
- **The conjectures.** Conjecture turns the bounds into the refutations.

### Soundness and scope

- **No added assumptions.** The development has no `sorry`/`admit` placeholders and adds
  no axioms. The recorded axiom audit (`validation/axioms.txt`) uses only `propext`,
  `Classical.choice` and `Quot.sound`.
- **What is cited, not formalised.** The book's general best-uniform-process theorem
  (4F.1) is cited in the manuscript; the abstract theory of uniform processes is not
  re-formalised here. The refutations need no such theory, because they are stated
  about intrinsic complexities defined directly from certificates.
- **What is cited, continued.** The paper also cites the known lower bounds
  (van den Dries–Moschovakis); they are not formalised either.
- **Conventions.** Coprimeness in the refutations is the book's relation, which requires
  positive inputs. The reduction to D (`CoprimeCertificate`, `RemainderList`) uses
  `Nat.Coprime`; `callsCoprimeness_eq_callsRem` connects the two on positive coprime
  inputs. For non-coprime inputs, D and `callsRem` are 0 only because their defining sets
  are empty.

## Reproducing finite checks

```
python3 scripts/check_certificates.py
python3 remainder_only_certificate.py
python3 scripts/check_prefix_lemma.py
```

- **`scripts/check_certificates.py`** runs a 310-case suite. It covers zero inputs, equal
  inputs, scaled non-coprime inputs, random large inputs and Fibonacci pairs. It also
  checks that four invalid traces are rejected.
- **`remainder_only_certificate.py`** reproduces the three numerical examples in the
  manuscript.
- **`scripts/check_prefix_lemma.py`** checks the Euclidean-prefix lemma exhaustively for
  every coprime pair with 3 ≤ a < 1500 and 1 ≤ b < a, every prefix length, and up to
  60 consecutive moduli above the threshold 2a/r_h, restricted to m < 4a. This gives
  254,722,179 instances. A failure exits with a nonzero status and reports the first
  counterexample. As a control it also counts collisions when the threshold is dropped.

Results are in `validation/`. The planner uses unrestricted arithmetic; only the
remainder facts it returns are counted as instructions. These finite checks supplement
the Lean proof.

## Nondeterministic program family

Section 6 of the paper proves the program-family theorem. The expanded
[research note](research/nondeterministic-prefix.pdf)
([source](research/nondeterministic-prefix.tex)) gives the implementation details
and executable checks for this family of finite
nondeterministic recursive gcd programs using only remainder and the zero test.
For each integer p ≥ 1, a program with 4ᵖ + 5 generator parameters has worst-case
remainder cost at most (3/p + o(1)) log₂ a. Thus, for every ε > 0, there is a
fixed program with cost at most ε log₂ a + Bε on all positive inputs a ≥ b.

**This does not give one sublogarithmic program.** The program depends on ε;
the Main Conjecture allows its lower-bound coefficient to depend on the program.
The note explains the remaining difficulty with reusing a growing Euclidean
prefix in one fixed first-order program.

**Formalization status:** the program-family bound is now checked in Lean,
including finite first-order syntax and call-by-value evaluation:

- `RegisterProgram.maxCost_step` proves the operational recurrence with a fixed
  tuple of h + 4 parameters and explicit recursive subcomputations.
- `RegisterProgram.Fixed.limsup_profile_le` proves the coefficient 3/p.
- `RegisterProgram.Syntax.run_invokes` and `accepts_eval` translate register runs
  into evaluations of the finite program, preserving remainder counts exactly.
- `RegisterProgram.Syntax.eval_head_correct` proves that every terminating
  evaluation returns the gcd; `eval_head_exists` proves a successful evaluation
  exists on every input.
- `RegisterProgram.Syntax.eventually_eval_bound` gives the uniform asymptotic
  bound, including verification. `arbitrarily_small_program` states the
  ε log₂ a + Bε bound with the program chosen before the inputs.
- `RegisterProgram.Syntax.Machine.eval_iff_steps` proves exact-cost equivalence
  between evaluation trees and a specialized two-stack small-step machine.
  `Step.context` proves transition locality. `head_correct` and `head_exists`
  give correctness of every terminating execution and existence on every input.
- `RegisterProgram.Syntax.Machine.eventually_steps_bound` and
  `arbitrarily_small_program` state the bounds directly for machine executions.

These names are in the `ShortGCD` namespace. The proof path is RegisterProgram →
RegisterMachine → RegisterPrefix → RegisterCost → RegisterRecurrence →
[RegisterAsymptotic](ShortGCD/RegisterAsymptotic.lean) →
[RegisterSyntax](ShortGCD/RegisterSyntax.lean) →
[RegisterSmallStep](ShortGCD/RegisterSmallStep.lean). All are included in `lake build`.
The [research entry point](research/RegisterProgram.lean) records a separate
[axiom audit](research/register-axioms.txt), using only the standard Lean axioms.

The syntax proof inlines the setter functions. Lean now also checks correspondence
with an explicit specialization of the book's two-stack machine, including
right-to-left argument order and separate zero-test and branch transitions.
Only remainder transitions carry a nonzero cost. This covers the language and
program family used here; the book's theory for arbitrary structures and the
Python interpreter are not formalized.
The [model and literature audit](research/model-novelty-audit.txt) records the
source checks and their limits. No matching uniform coefficient result was located
in the sources checked; this is not an exhaustive novelty determination.

The executable compiler produces finite first-order syntax, which a separate
interpreter executes using supplied nondeterministic choices. Checks cover 138
cases, 129 additional scaled replays, and eight negative cases; results are in
[register-validation.json](research/register-validation.json).

```
lake env lean research/RegisterProgram.lean
python3 research/check_register_program.py
python3 -O research/check_register_program.py
python3 research/register_program.py --width 9
```

Build the research PDF by running `pdflatex nondeterministic-prefix.tex` twice
from `research/`.

### Investigating one fixed sublogarithmic program

The [investigation](research/single-program-investigation.pdf)
([source](research/single-program-investigation.tex)) separates tested constructions,
restricted accounting results, and open questions. A new
[fixed program](research/rebuilding_program.py), of maximum arity three, can select
arbitrarily deep Euclidean-prefix operands by recomputing them. The same syntax
passes 270 runs and 270 scaled replays across different planning depths.
On the recorded 2,048-bit example, longer prefixes reduce the number of contractions
but increase the cost of rebuilding their operands.

The Lean lemma in [PrefixPolicies.lean](research/PrefixPolicies.lean) shows that a
fresh-prefix budget is at least four times its guaranteed bit progress, even with
varying prefix lengths. This limits that accounting argument; it is **not a lower
bound on the minimum cost of the program**, whose contractions can exceed the
guarantee. No single sublogarithmic program has been obtained.

```
lake env lean research/PrefixPolicies.lean
python3 research/rebuilding_program.py
python3 -O research/rebuilding_program.py
```

Build this note with two runs of `pdflatex single-program-investigation.tex`
from `research/`.

The note also proposes studying computation graphs with a fixed bound on
treewidth as a way to capture the restriction imposed by a finite program.
That direction is exploratory and is not part of the main paper's theorems.

## Shape-count reduction

The [shape-count note](research/shape-count.pdf) ([source](research/shape-count.tex))
reduces both open questions to one counting hypothesis. A *shape* is a remainder-only
derivation with operands named by position. A fixed recursive program, deterministic or
nondeterministic, produces at most C_P^(c+1) shapes with at most c remainder calls, against
((c+1)!)² for unrestricted derivations. If no shape of length at most c₀ log N reaches 1 on
more than N^(2−δ) pairs below N, then every fixed program needs r_P log a remainder calls on
almost all coprime pairs (an almost-all Main Conjecture for programs), and the
O(log a / log log a) bound is tight on almost all pairs. **The hypothesis is open.**

The unconditional parts are checked in Lean and included in `lake build` and the axiom
audit:

- `ShortGCD.GeneralPrograms.compile`, `eval_shape` and `card_shapeSet_le_pow`: the
  Shape-Count Lemma for general recursive programs of bounded arity.
- `ShortGCD.GeneralPrograms.card_eval_le`, `card_decide_le` and
  `eventually_card_eval_le`: the counting reduction for gcd and coprimeness.
- `ShortGCD.ShapeCount.card_run_le` and `eventually_card_run_le`: the same for the
  register programs of the program family.
- `ShortGCD.TightnessReduction.eventually_card_within_le`: the conditional tightness
  statement for D.

Build the note with two runs of `pdflatex shape-count.tex` from `research/`.

## Building the paper

```
cd paper
pdflatex euclid-uniform-processes.tex
pdflatex euclid-uniform-processes.tex
```

The second run resolves cross-references. The bibliography is written inline, so no
BibTeX run is needed.

## License

Apache License 2.0; see `LICENSE`.
