module

public import ShortGCD

@[expose] public section

/-!
# Solution

Every declaration named in `comparator.json` is defined and proved in the `ShortGCD`
library under the same name, with the statement given in `Challenge.lean`. The main
results are in `ShortGCD.SharpBound` (`uniform_real_bound_six`),
`ShortGCD.SharpCertificates` (`uniform_intrinsic_bound_six`), `ShortGCD.Conjecture` (the
refutations), `ShortGCD.LowerBounds` (certificate existence and the lower bounds),
`ShortGCD.TailSource` (the bounded-memory register programs, in the syntax of
`ShortGCD.RegisterProgram`), `ShortGCD.ClosureDepth`
(the closure-depth question) and `ShortGCD.BookCertificates` (the book's certificates).
-/
