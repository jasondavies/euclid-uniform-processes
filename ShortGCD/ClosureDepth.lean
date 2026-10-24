module

public import ShortGCD.Asymptotic

@[expose] public section

/-! # Closure depth of the gcd

Van den Dries and Moschovakis, *Arithmetic complexity* (ACM TOCL 10(1), 2009), measure the
parallel depth of the gcd (p. 2:6). Starting from `S₀ = {0, 1, a, b}`, each stage adjoins
`x + y`, `x - y`, `iq(x, y)` and `rem(x, y)` for all `x, y` in the previous stage, and
`g(a, b)` is the least stage containing `gcd(a, b)`. Their conventions (p. 2:4) are
`iq(a, b) = ⌊a / b⌋` and `rem(a, b) = a - b·iq(a, b)`, extended by `iq(a, 0) = a` and
`rem(a, 0) = a`. They ask (Open Problem, p. 2:11) whether there are positive integers
`αₙ → ∞` and `βₙ` and a `C > 0` with `g(αₙ, βₙ) > C log αₙ` for all `n`.

A remainder derivation from `a, rem(b, a)` of length `n` stays inside stage `n + 1`, so
`g(a, b) ≤ 1 + G(a, rem(b, a))`, which is `O(log a / log log a)` uniformly in `b`. Hence no
such sequences exist.
-/

open Filter Topology

namespace ShortGCD.ClosureDepth

/-- Integer quotient `⌊a / b⌋`, with `iq(a, 0) = a`. -/
def iq (a b : ℤ) : ℤ := if b = 0 then a else ⌊(a : ℚ) / b⌋

/-- Remainder `a - b·iq(a, b)`; in particular `rem(a, 0) = a`. -/
def rem (a b : ℤ) : ℤ := a - b * iq a b

/-- The closure stages `S_k(a, b)`. -/
def stage (a b : ℤ) : ℕ → Set ℤ
  | 0 => {0, 1, a, b}
  | k+1 => stage a b k ∪ {z | ∃ x ∈ stage a b k, ∃ y ∈ stage a b k,
      z = x + y ∨ z = x - y ∨ z = iq x y ∨ z = rem x y}

/-- The closure depth `g(a, b)`: the least stage containing `gcd(a, b)`. -/
noncomputable def depth (a b : ℤ) : ℕ := sInf {k | (Int.gcd a b : ℤ) ∈ stage a b k}

lemma stage_mono (a b : ℤ) {k l : ℕ} (h : k ≤ l) : stage a b k ⊆ stage a b l := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Set.subset_union_left

lemma rem_add_mem {a b : ℤ} {k : ℕ} {x y : ℤ} (hx : x ∈ stage a b k) (hy : y ∈ stage a b k) :
    rem x y ∈ stage a b (k+1) :=
  Or.inr ⟨x, hx, y, hy, Or.inr (Or.inr (Or.inr rfl))⟩

/-- At positive divisors the source's remainder is the usual one on natural numbers. -/
lemma rem_natCast (x y : ℕ) (hy : 0 < y) : rem x y = ((x % y : ℕ) : ℤ) := by
  have hy' : (y : ℤ) ≠ 0 := by exact_mod_cast hy.ne'
  have hfloor : ⌊((x : ℤ) : ℚ) / ((y : ℤ) : ℚ)⌋ = (x : ℤ) / (y : ℤ) := by
    rw [show ((y : ℤ) : ℚ) = (y : ℚ) by simp]
    exact Rat.floor_intCast_div_natCast x y
  simp only [rem, iq, hy', ↓reduceIte, hfloor]
  rw [← Int.emod_def]
  exact (Int.natCast_mod x y).symm

/-- A remainder derivation of length `n` from values in stage `k` stays in stage `k + n`. -/
lemma derives_stage {a b : ℤ} {S T : Finset ℕ} {n k : ℕ} (h : Derives S n T)
    (hS : ∀ x ∈ S, (x : ℤ) ∈ stage a b k) : ∀ x ∈ T, (x : ℤ) ∈ stage a b (k + n) := by
  induction h with
  | refl => simpa using hS
  | @step T n x y hd hx hy hp ih =>
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · rw [show k + (n + 1) = (k + n) + 1 by omega, ← rem_natCast x y hp]
      exact rem_add_mem (ih x hx) (ih y hy)
    · exact stage_mono a b (by omega) (ih z hz)

/-- For `a > 0`, the gcd lies in stage `1 + G(a, rem(b, a))`. -/
lemma gcd_mem_stage (a b : ℕ) (ha : 0 < a) :
    (Int.gcd a b : ℤ) ∈ stage a b (1 + G a (b % a)) := by
  obtain ⟨n, T, hn, hd, hw⟩ := generates_G a (b % a)
  have hS : ∀ x ∈ ({a, b % a} : Finset ℕ), (x : ℤ) ∈ stage a b 1 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inl (by simp [stage])
    · rw [Finset.mem_singleton.mp hx, ← rem_natCast b a ha]
      exact rem_add_mem (by simp [stage]) (by simp [stage])
  have hg : Nat.gcd a (b % a) = Nat.gcd a b := by
    rw [Nat.gcd_comm a (b % a), ← Nat.gcd_rec, Nat.gcd_comm]
  have hmem := derives_stage hd hS _ hw
  rw [hg] at hmem
  show ((Int.gcd (a : ℤ) (b : ℤ) : ℕ) : ℤ) ∈ stage a b (1 + G a (b % a))
  rw [Int.gcd_natCast_natCast]
  exact stage_mono a b (by omega) hmem

/-- **Closure depth is at most one more than the derivation length.** For `a > 0`,
`g(a, b) ≤ 1 + G(a, rem(b, a))`. -/
theorem depth_le (a b : ℕ) (ha : 0 < a) : depth a b ≤ 1 + G a (b % a) :=
  Nat.sInf_le (gcd_mem_stage a b ha)

/-- **The closure depth is attained**: for `a > 0`, `gcd(a, b)` lies in stage `g(a, b)`, so
`g(a, b)` is a genuine least stage and not the default value of an empty infimum. -/
theorem depth_mem (a b : ℕ) (ha : 0 < a) : (Int.gcd a b : ℤ) ∈ stage a b (depth a b) :=
  Nat.sInf_mem (s := {k | (Int.gcd (a : ℤ) (b : ℤ) : ℤ) ∈ stage a b k})
    ⟨_, gcd_mem_stage a b ha⟩

/-- **The closure depth is `O(log a / log log a)`**, uniformly in `b ≥ 1`. -/
theorem depth_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ, 4 ≤ a → 1 ≤ b →
    (depth a b : ℝ) ≤ 1 + C * (Real.logb 2 a / Real.logb 2 (Real.logb 2 a)) := by
  obtain ⟨C, hC, h⟩ := uniform_real_bound
  refine ⟨C, hC, fun a b ha _ => ?_⟩
  have h1 : (depth a b : ℝ) ≤ 1 + (G a (b % a) : ℝ) := by
    exact_mod_cast depth_le a b (by omega)
  have h2 := h a (b % a) ha (Nat.mod_lt _ (by omega)).le
  linarith

/-- **Answer to the Open Problem of van den Dries and Moschovakis.** There are no positive
integers `αₙ → ∞`, `βₙ` and `C > 0` with `g(αₙ, βₙ) > C log₂ αₙ` for all `n`. -/
theorem no_logarithmic_sequences :
    ¬ ∃ (α β : ℕ → ℕ) (C : ℝ), 0 < C ∧ Tendsto α atTop atTop ∧
      (∀ n, 0 < α n ∧ 0 < β n) ∧ ∀ n, C * Real.logb 2 (α n) < depth (α n) (β n) := by
  rintro ⟨α, β, C, hC, hα, hpos, hgt⟩
  have hlog : Tendsto (fun a : ℕ => Real.logb 2 (a : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ a : ℕ in atTop, (sizeCost a : ℝ) ≤ C / 2 * Real.logb 2 a := by
    filter_upwards [sizeCost_isLittleO_log.bound (half_pos hC), eventually_ge_atTop 1]
      with a ha ha1
    have hl : 0 ≤ Real.logb 2 (a : ℝ) :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast ha1)
    simpa [Real.norm_eq_abs, abs_of_nonneg hl] using ha
  have hone : ∀ᶠ a : ℕ in atTop, 1 < C / 2 * Real.logb 2 a :=
    (hlog.const_mul_atTop (half_pos hC)).eventually (eventually_gt_atTop 1)
  obtain ⟨n, hn1, hn2⟩ := (hα.eventually (hsmall.and hone)).exists
  have ha := (hpos n).1
  have hd : (depth (α n) (β n) : ℝ) ≤ 1 + (sizeCost (α n) : ℝ) := by
    have := (depth_le (α n) (β n) ha).trans
      (Nat.add_le_add_left (G_le_sizeCost le_rfl (Nat.mod_lt _ ha).le) 1)
    exact_mod_cast this
  have := hgt n
  linarith

end ShortGCD.ClosureDepth
