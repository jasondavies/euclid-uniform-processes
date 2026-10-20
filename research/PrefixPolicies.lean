import ShortGCD.RegisterSmallStep

/-! # Accounting for a fresh prefix at each contraction

This is an analysis of one restricted proof policy, not a lower bound on
actual remainder computations. A prefix with `h = 4^p + 1` ordered pairs
uses `h - 1 = 4^p` new Euclidean calls when rebuilt from its initial pair.
The residue-count argument guarantees `p` bits of contraction. If a policy
discards this prefix after one contraction, even varying `p` cannot make
its charged construction budget sublinear in the guaranteed progress.
Actual contractions can be much larger than the guarantee.
-/

namespace ShortGCD.PrefixPolicies

def rebuildCharge (ps : List ℕ) : ℕ := (ps.map (fun p => 4^p)).sum
def guaranteedProgress (ps : List ℕ) : ℕ := ps.sum

lemma four_mul_le_pow {p : ℕ} (hp : 0 < p) : 4*p ≤ 4^p := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  induction q with
  | zero => norm_num
  | succ q ih =>
    have ih' := ih (by omega)
    simp only [Nat.succ_eq_add_one] at *
    rw [pow_succ]
    nlinarith

/-- For every list `ps` of positive integers, `4 * ∑ p ≤ ∑ 4^p`: the rebuilding charge is at
least four times the guaranteed progress. -/
theorem rebuild_charge_ge_four_progress (ps : List ℕ) (hp : ∀ p ∈ ps, 0 < p) :
    4*guaranteedProgress ps ≤ rebuildCharge ps := by
  induction ps with
  | nil => simp [guaranteedProgress, rebuildCharge]
  | cons p ps ih =>
    have hfirst := four_mul_le_pow (hp p (by simp))
    have hrest := ih (fun q hq => hp q (by simp [hq]))
    simp only [guaranteedProgress, rebuildCharge, List.sum_cons, List.map_cons] at *
    omega

/-- A target justified solely by the accumulated guarantees has a linear
rebuilding charge. This says nothing about other programs or sharper analyses. -/
theorem target_charge {target : ℕ} {ps : List ℕ} (hp : ∀ p ∈ ps, 0 < p)
    (ht : target ≤ guaranteedProgress ps) : 4*target ≤ rebuildCharge ps :=
  (Nat.mul_le_mul_left 4 ht).trans (rebuild_charge_ge_four_progress ps hp)

end ShortGCD.PrefixPolicies

#print axioms ShortGCD.PrefixPolicies.rebuild_charge_ge_four_progress
#print axioms ShortGCD.PrefixPolicies.target_charge
