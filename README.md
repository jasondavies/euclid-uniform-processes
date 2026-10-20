# The Euclidean algorithm is not optimal among uniform processes

**Proved.** gcd(a, b) has a remainder-only derivation with
(6 + o(1)) log₂ a / log₂ log₂ a remainder calls, uniformly in 0 ≤ b ≤ a (Euclid needs
about 1.44 log₂ a in the worst case). Hence the intrinsic calls(rem)-complexity of gcd
and coprimeness is o(log a). Also: an Ω(log log a) lower bound on almost all coprime
pairs, and, for each ε > 0, a fixed nondeterministic gcd program with cost at most
ε log₂ a + Bε.

**Refuted.** Conjecture 3.4 of Moschovakis's 2012 notes and the precise version (4F-5) of
the Main Conjecture in his 2019 book; with the cited Theorem 4F.1, also the possibility
raised on p. 188 that the Main Conjecture holds for all uniform processes of Nε.

**Open.** The Main Conjecture for algorithms. No single sublogarithmic program is known.

**Verified.** Everything above is machine-checked in Lean 4, except the step that uses the
cited Theorem 4F.1. The result has not yet been reviewed by an expert in the area.

Read the paper: [euclid-uniform-processes.pdf](paper/euclid-uniform-processes.pdf).

## Results

Logarithmic remainder-call lower bounds for gcd and coprimeness cannot follow from
uniformity alone. Every pair a ≥ b has a remainder-only derivation of gcd(a, b) using
O(log a / log log a) remainder calls. Each call takes the remainder of two values
already available, starting from a and b; earlier values are kept and no numerical
constants are introduced. Euclid needs about 1.44 log₂ a calls in the worst case
(successive Fibonacci numbers).

**Notation.** G(a, b) is the least number of remainder calls in such a derivation of
gcd(a, b), and D(a, b) is G(a, b) on coprime inputs, the length of a shortest remainder
derivation of 1. Nε = (N, rem, eq0, eq1) is the Euclidean structure, ⊥⊥ is the
coprimeness relation (x, y ≥ 1 and gcd(x, y) = 1), and calls(rem) counts remainder
calls. A remainder fact in a certificate corresponds to a remainder call.

The refined upper bound is **(6 + o(1)) log₂ a / log₂ log₂ a**, uniformly in b.
Precisely, for every ε > 0, the coefficient 6 + ε works for all sufficiently large a
and every 0 ≤ b ≤ a. The same leading coefficient holds for the intrinsic
remainder-call complexities below on positive inputs. No optimality of 6 is claimed.

As a consequence, the intrinsic calls(rem)-complexity of both coprimeness and gcd in
Nε is o(log a), uniformly over pairs with 1 ≤ b ≤ a. This refutes the uniform-process
form of van den Dries and Moschovakis's conjecture that the Euclidean algorithm is
optimal among its peers:

- **Conjecture 3.4** of Moschovakis's 2012 notes, *Absolute lower bounds for uniform
  processes*: there is no r > 0 with calls(rem)(Nε, ⊥⊥, a, b) ≥ r log a for infinitely
  many a ≥ b ≥ 1. The exact wording (rational r, infinitely many a) is refuted too.
- **The "precise version" (4F-5) of the Main Conjecture** in *Abstract Recursion and
  Intrinsic Complexity* (2019, p. 151): there is no K > 0 with
  2 log max(x, y) ≤ K · calls(rem)(gcd, x, y) on infinitely many pairs. This holds both
  for gcd certificates without eq1 facts and for certificates in Nε. The book's form,
  with a set D on which the complexity is unbounded (condition (4F-4)), is refuted as
  well. That statement drops the book's first inequality, calls(rem)(ε, x, y) ≤ L(x, y),
  which only makes the refuted statement weaker.
- **The possibility raised after Corollary 6C.7 (p. 188)**, that the Main Conjecture
  "holds for all uniform processes of Nε". Ruling this out also uses the book's
  best-uniform-process theorem (4F.1), which turns a small intrinsic complexity into a
  uniform process with that complexity. Theorem 4F.1 is cited, not formalized.

On the lower-bound side, D(a, b) > (1 − ε) log₂ log₂ N for all but o(N²) coprime pairs,
so the Ω(log log a) lower bound holds on almost all coprime pairs, not only on the
book's difficult pairs.

**A further algorithmic result:** for every ε > 0, there is a fixed finite
nondeterministic recursive gcd program using only rem and eq0 with cost at most
ε log₂ a + Bε on all positive inputs a ≥ b. Cost is the minimum number of remainder
calls over successful computations; every terminating computation is correct.
The program depends on ε, so this family does not give one sublogarithmic program.
See [Nondeterministic program family](#nondeterministic-program-family).

What remains open:

- **The Main Conjecture for algorithms.** The result shows that a proof of it must use
  properties beyond uniformity.
- **Operand choice is not charged.** The construction gives no remainder-only algorithm,
  deterministic or nondeterministic, with this cost: choosing which two stored residues
  to combine is free. The book's best-uniform-process theorem (4F.1) supplies a uniform
  process attaining the bound.
- **The homomorphism-test barrier.** The Homomorphism Test applied to all generated
  primitive operation diagrams cannot prove a logarithmic lower bound: every input has a
  certificate with o(log a) remainder facts. This leaves open arguments combining
  homomorphisms with additional restrictions on computations.
- **The stored prefix.** A nondeterministic program would still need to implement
  reusable access to the growing stored prefix within the claimed cost.

Page citations refer to the published edition of Moschovakis, *Abstract Recursion and
Intrinsic Complexity* (Lecture Notes in Logic 48, Cambridge University Press / ASL, 2019,
doi:10.1017/9781108234238). The paper
[euclid-uniform-processes.pdf](paper/euclid-uniform-processes.pdf) is built from
[euclid-uniform-processes.tex](paper/euclid-uniform-processes.tex).

## Lean verification

**Status.** The upper bounds, including the leading coefficient 6, the finite
nondeterministic program-family bound, and the refutations of Conjecture 3.4 and
(4F-5) are machine-checked in Lean, as listed below, as is the almost-all
Ω(log log a) lower bound. The consequence for the question on p. 188 also uses the
cited Theorem 4F.1. A second, independent Lean formalization of the original Big-O
argument was developed separately.

The project pins Lean and mathlib to v4.35.0. On a fresh checkout with elan:

```sh
lake exe cache get
lake build
lake env lean validation/Axioms.lean
```

**Definitions.** The intrinsic complexities `callsCoprimeness`, `callsGcd` and
`callsRemGcd` are defined directly from certificates. A certificate is a finite partial
substructure generated by the input, such that every map preserving its facts respects
the relation or function. Coprimeness is the book's relation `BookCoprime`: x, y ≥ 1 and
gcd(x, y) = 1. All names below are in the `ShortGCD` namespace.

### Refutations

The (4F-5) statements cover all pairs in ℕ², including pairs with a zero entry, which
need no remainder facts (`callsGcd_zero_left`, `callsGcd_zero_right`).

| Statement | Lean name |
| --- | --- |
| Conjecture 3.4 is false | `ShortGCD.not_conjecture_3_4` |
| Conjecture 3.4, exact wording (rational r, infinitely many a) | `ShortGCD.not_conjecture_3_4_literal` |
| (4F-5) is false, gcd certificates without eq1 facts | `ShortGCD.not_main_conjecture_4F5` |
| (4F-5) is false, certificates in Nε | `ShortGCD.not_main_conjecture_4F5_Neps` |
| (4F-5) in the book's form, with an unbounded set D (condition (4F-4)) | `ShortGCD.not_main_conjecture_4F5_literal` |

### Upper bounds

| Statement | Lean name |
| --- | --- |
| For every ε > 0, eventually in a, 6 + ε bounds G(a, b) / (log₂ a / log₂ log₂ a) for every b ≤ a | `ShortGCD.uniform_real_bound_six` |
| The same for `callsCoprimeness`, `callsGcd` and `callsRemGcd`, for every positive b ≤ a | `ShortGCD.uniform_intrinsic_bound_six` |
| The upper limit of sizeCost(2ⁿ) · log₂ n / n is at most 6 | `ShortGCD.Sharp.limsup_profile_le_six` |
| The same, absorbing any fixed additive instruction overhead | `eventually_sizeCost_add_le_six` |
| One real constant C bounds G(a, b) by C · logb 2 a / logb 2 (logb 2 a), for every a ≥ 4 and b ≤ a | `ShortGCD.uniform_real_bound` |
| Worst-case Big-O and little-o statements, taking the maximum over all smaller inputs | `ShortGCD.sizeCost_isBigO`, `ShortGCD.sizeCost_isLittleO_log` |
| For every ε > 0, eventually in M, `callsCoprimeness` and `callsGcd` are at most ε log₂ M on all pairs with 0 < a, b ≤ M | `ShortGCD.eventually_calls_le` |

### Certificates and reductions

| Statement | Lean name |
| --- | --- |
| On coprime pairs, the least number of remainder facts in a certificate for `Nat.Coprime` equals D(a, b); the doubling map u ↦ 2u shows every certificate must reach 1 | `ShortGCD.callsRem_eq_D` |
| Adding eq0(a) = ff and eq0(b) = ff turns a `Nat.Coprime` certificate into one for the book's relation, with the same remainder facts | `ShortGCD.certifiesCoprimeness_of_certifiesCoprime` |
| So for positive coprime inputs the two complexities agree | `ShortGCD.callsCoprimeness_eq_callsRem` |
| Allowing eq1 facts can only lower the gcd complexity | `ShortGCD.callsRemGcd_le_callsGcd` |
| Generated gcd certificates with at most the same bound plus two remainder facts, and no eq1 facts | `ShortGCD.uniform_gcd_certificates` |
| For a, b ≥ 1, the book's coprimeness relation has a certificate with at most G(a, b) + 2 remainder facts, for either truth value | `ShortGCD.callsCoprimeness_le` |
| True instances of `Nat.Coprime`: at most G(a, b) | `coprime_certificate_bound` |
| False instances, a > 0: at most G(a, b) + 2 | `noncoprime_certificate_bound` |
| G agrees with D, the list-derivation definition, on coprime inputs | `ShortGCD.G_eq_D` |

### Lower bounds

| Statement | Lean name |
| --- | --- |
| Every generated gcd certificate has at least G(a, b) remainder facts | `ShortGCD.gcd_certificate_lower` |
| At most 40 (2 + ln N) N^(2 − 2^(−d)) pairs 2 ≤ b < a ≤ N have a derivation of 1 of length at most d | `ShortGCD.AlmostAll.card_within_le` |
| D(a, b) > (1 − ε) log₂ log₂ N for all but o(N²) coprime pairs | `ShortGCD.AlmostAll.tendsto_card_within_loglog` |

### Module structure

Arrows point from a module to the modules that import it (all in [ShortGCD/](ShortGCD/)).
Derivation, Prefix, Arithmetic and CoprimeCertificate import only Mathlib. The root
[ShortGCD.lean](ShortGCD.lean) imports Asymptotic, Certificates, Conjecture,
SharpCertificates, RegisterSmallStep and AlmostAll.

```
Certificates and the reduction
  CoprimeCertificate → RemainderList → GcdCertificate → Certificates, AlmostAll

The upper bound
  Derivation → Composition → Normalization
  Derivation → Gap
  Gap, Composition, Prefix → Contraction
  Contraction, Normalization → Euclid → FiniteBound
  FiniteBound, Arithmetic → UpperBound → Asymptotic → SharpBound

Both strands meet
  Asymptotic, GcdCertificate → Certificates → Conjecture
  SharpBound, Conjecture → SharpCertificates

The program family
  Derivation → RegisterProgram
  RegisterProgram, Euclid → RegisterMachine → RegisterPrefix → RegisterCost
    → RegisterRecurrence
  RegisterRecurrence, SharpBound → RegisterAsymptotic → RegisterSyntax
    → RegisterSmallStep
```

- **The finite recurrence.** The core is `sizeCost_step` (in FiniteBound). Its
  hypotheses concern natural-number size parameters, not an assumed complexity bound.
- **The bound.** Arithmetic discharges those hypotheses, and UpperBound proves the
  resulting bound by strong induction.
- **The logarithms.** Asymptotic compares integer logarithms with real logarithms.
- **The leading coefficient.** SharpBound reuses `sizeCost_step` with tunable prefix
  and recursive-size parameters. The original Big-O theorem supplies boundedness;
  an upper-limit argument gives 6, and rounding limits preserve it for general inputs.
- **The conjectures.** Conjecture turns the bounds into the refutations;
  SharpCertificates combines the refined bound with the certificate reductions.

### Soundness and scope

- **No added assumptions.** The development has no `sorry`/`admit` placeholders and adds
  no axioms. The recorded axiom audit ([axioms.txt](validation/axioms.txt)) uses only
  `propext`, `Classical.choice` and `Quot.sound`.
- **What is cited, not formalized.** The book's general best-uniform-process theorem
  (4F.1) is cited in the manuscript; the abstract theory of uniform processes is not
  re-formalized here. The refutations need no such theory, because they are stated
  about intrinsic complexities defined directly from certificates. The paper also cites
  the known lower bounds (van den Dries–Moschovakis); they are not formalized either.
- **Conventions.** Coprimeness in the refutations is the book's relation, which requires
  positive inputs. The reduction to D (`CoprimeCertificate`, `RemainderList`) uses
  `Nat.Coprime`; `callsCoprimeness_eq_callsRem` connects the two on positive coprime
  inputs. For non-coprime inputs, D and `callsRem` are 0 only because their defining sets
  are empty.

## Finite checks

```sh
python3 scripts/check_certificates.py
python3 remainder_only_certificate.py
python3 scripts/check_prefix_lemma.py
```

- **[check_certificates.py](scripts/check_certificates.py)** runs a 310-case suite. It
  covers zero inputs, equal inputs, scaled non-coprime inputs, random large inputs and
  Fibonacci pairs. It also checks that four invalid traces are rejected.
- **[remainder_only_certificate.py](remainder_only_certificate.py)** reproduces the three
  numerical examples in the manuscript.
- **[check_prefix_lemma.py](scripts/check_prefix_lemma.py)** checks the Euclidean-prefix
  lemma exhaustively for every coprime pair with 3 ≤ a < 1500 and 1 ≤ b < a, every prefix
  length, and up to 60 consecutive moduli above the threshold 2a/r_h, restricted to
  m < 4a. This gives 254,722,179 instances. A failure exits with a nonzero status and
  reports the first counterexample. As a control it also counts collisions when the
  threshold is dropped.

Results are in [validation/](validation/). The planner uses unrestricted arithmetic; only
the remainder facts it returns are counted as instructions. These finite checks
supplement the Lean proof.

## Nondeterministic program family

For each integer p ≥ 1, a finite nondeterministic recursive gcd program using only
remainder and the zero test, with 4ᵖ + 5 generator parameters, has worst-case remainder
cost at most (3/p + o(1)) log₂ a. Thus, for every ε > 0, there is a fixed program with
cost at most ε log₂ a + Bε on all positive inputs a ≥ b. The paper proves this in the
section "Fixed programs with arbitrarily small coefficients"; the expanded research note
[nondeterministic-prefix.pdf](research/nondeterministic-prefix.pdf)
([source](research/nondeterministic-prefix.tex)) gives implementation details and
executable checks. **This does not give one sublogarithmic program**: the program
depends on ε, and the Main Conjecture allows its lower-bound coefficient to depend on the
program. The note explains the remaining difficulty with reusing a growing Euclidean
prefix in one fixed first-order program.

The bound is checked in Lean, including finite first-order syntax and call-by-value
evaluation. The names below are in the `ShortGCD` namespace; the modules run from
RegisterProgram to [RegisterAsymptotic](ShortGCD/RegisterAsymptotic.lean),
[RegisterSyntax](ShortGCD/RegisterSyntax.lean) and
[RegisterSmallStep](ShortGCD/RegisterSmallStep.lean), all included in `lake build`.

| Statement | Lean name |
| --- | --- |
| Operational recurrence with a fixed tuple of h + 4 parameters and explicit recursive subcomputations | `RegisterProgram.maxCost_step` |
| The coefficient 3/p | `RegisterProgram.Fixed.limsup_profile_le` |
| Register runs translate into evaluations of the finite program, preserving remainder counts exactly | `RegisterProgram.Syntax.run_invokes`, `accepts_eval` |
| Every terminating evaluation returns the gcd | `RegisterProgram.Syntax.eval_head_correct` |
| A successful evaluation exists on every input | `eval_head_exists` |
| Uniform asymptotic bound, including verification | `RegisterProgram.Syntax.eventually_eval_bound` |
| The ε log₂ a + Bε bound with the program chosen before the inputs | `arbitrarily_small_program` |
| Exact-cost equivalence between evaluation trees and a specialized two-stack small-step machine | `RegisterProgram.Syntax.Machine.eval_iff_steps` |
| Transition locality | `Step.context` |
| Correctness of every terminating execution; existence on every input | `head_correct`, `head_exists` |
| The bounds stated directly for machine executions | `RegisterProgram.Syntax.Machine.eventually_steps_bound`, `arbitrarily_small_program` |

The [research entry point](research/RegisterProgram.lean) records a separate
[axiom audit](research/register-axioms.txt), using only the standard Lean axioms.

The syntax proof inlines the setter functions. Lean also checks correspondence with an
explicit specialization of the book's two-stack machine (right-to-left argument order,
separate zero-test and branch transitions, nonzero cost only on remainder transitions);
this covers the language and program family used here. The book's theory for arbitrary
structures and the Python interpreter are not formalized. The
[model-novelty-audit.txt](research/model-novelty-audit.txt) records the source checks and
their limits: no matching uniform coefficient result was located in the sources checked,
which is not an exhaustive novelty determination.

The executable compiler produces finite first-order syntax, which a separate interpreter
executes using supplied nondeterministic choices. Checks cover 138 cases, 129 additional
scaled replays, and eight negative cases; results are in
[register-validation.json](research/register-validation.json).

```sh
lake env lean research/RegisterProgram.lean
python3 research/check_register_program.py
python3 -O research/check_register_program.py
python3 research/register_program.py --width 9
```

## Research notes (exploratory)

These notes are not part of the main paper's theorems.

- **[nondeterministic-prefix.pdf](research/nondeterministic-prefix.pdf)** expands the
  program-family construction above, with implementation details and executable checks.
- **[single-program-investigation.pdf](research/single-program-investigation.pdf)**
  ([source](research/single-program-investigation.tex)) separates tested constructions,
  restricted accounting results, and open questions about one fixed sublogarithmic
  program. A [fixed program](research/rebuilding_program.py) of maximum arity three
  selects arbitrarily deep Euclidean-prefix operands by recomputing them; the same syntax
  passes 270 runs and 270 scaled replays across different planning depths. On the
  recorded 2,048-bit example, longer prefixes reduce the number of contractions but
  increase the cost of rebuilding their operands. The Lean lemma in
  [PrefixPolicies.lean](research/PrefixPolicies.lean) shows that a fresh-prefix budget is
  at least four times its guaranteed bit progress, even with varying prefix lengths. This
  limits that accounting argument; it is **not a lower bound on the minimum cost of the
  program**, whose contractions can exceed the guarantee. The note also proposes studying
  computation graphs with a fixed bound on treewidth as a way to capture the restriction
  imposed by a finite program. No single sublogarithmic program has been obtained.
- **[model-novelty-audit.txt](research/model-novelty-audit.txt)** records the model
  correspondence checks and the bounded literature search for the program family.

```sh
lake env lean research/PrefixPolicies.lean
python3 research/rebuilding_program.py
python3 -O research/rebuilding_program.py
```

## Repository layout

- [ShortGCD/](ShortGCD/) and [ShortGCD.lean](ShortGCD.lean): the Lean development.
- [paper/](paper/): the manuscript.
- [research/](research/): exploratory notes, their Lean files, scripts and results.
- [scripts/](scripts/): finite checks for the main results.
- [validation/](validation/): axiom audit, build log and check results.
- [remainder_only_certificate.py](remainder_only_certificate.py): the numerical examples
  in the manuscript.

## Building the paper and notes

```sh
(cd paper && pdflatex euclid-uniform-processes.tex && pdflatex euclid-uniform-processes.tex)
(cd research && pdflatex nondeterministic-prefix.tex && pdflatex nondeterministic-prefix.tex)
(cd research && pdflatex single-program-investigation.tex \
  && pdflatex single-program-investigation.tex)
```

The second run resolves cross-references. The bibliography is written inline, so no
BibTeX run is needed.

## License

Apache License 2.0; see [LICENSE](LICENSE).
