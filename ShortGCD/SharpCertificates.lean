import ShortGCD.SharpBound
import ShortGCD.Conjecture

/-! # Leading constant six for intrinsic remainder-call complexity

The fixed certificate overhead does not alter the leading coefficient.
Coprimeness here is the book's predicate, requiring both inputs to be positive.
-/

open Filter

namespace ShortGCD

/-- The same coefficient `6 + ε` eventually bounds all three book-facing
intrinsic complexities, uniformly over positive second inputs. -/
theorem uniform_intrinsic_bound_six {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℕ in atTop, ∀ b : ℕ, 0 < b → b ≤ a →
      (callsCoprimeness a b : ℝ) ≤
        (6+ε) * (Real.logb 2 a / Real.logb 2 (Real.logb 2 a)) ∧
      (callsGcd a b : ℝ) ≤
        (6+ε) * (Real.logb 2 a / Real.logb 2 (Real.logb 2 a)) ∧
      (callsRemGcd a b : ℝ) ≤
        (6+ε) * (Real.logb 2 a / Real.logb 2 (Real.logb 2 a)) := by
  filter_upwards [eventually_sizeCost_add_le_six 2 (show 6 < 6+ε by linarith),
    eventually_ge_atTop 1] with a ha ha1
  intro b hb hba
  have hG : G a b + 2 ≤ sizeCost a + 2 := Nat.add_le_add_right (G_le_sizeCost le_rfl hba) 2
  have hgcd := (Nat.cast_le.mpr ((callsGcd_le (by omega : 0 < a)).trans hG)).trans
    (show ((sizeCost a + 2 : ℕ) : ℝ) ≤ _ from by simpa using ha)
  refine ⟨?_, hgcd, (Nat.cast_le.mpr (callsRemGcd_le_callsGcd a b)).trans hgcd⟩
  exact (Nat.cast_le.mpr ((callsCoprimeness_le (by omega) hb).trans hG)).trans
    (by simpa using ha)

end ShortGCD
