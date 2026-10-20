import ShortGCD.UpperBound

/-! # The uniform bound with real logarithms

`T̂(a) ≤ C log₂ a / log₂ log₂ a` for `a ≥ 4`, hence the same bound for `G a b` with `b ≤ a`,
and the asymptotic forms `sizeCost_isBigO` and `sizeCost_isLittleO_log`. These feed the
certificate bounds (`Certificates`, `Conjecture`) and the leading-coefficient refinement
(`SharpBound`).
-/

namespace ShortGCD

/-- Some `C > 0` satisfies `T̂(a) ≤ C log₂ a / log₂ log₂ a` for every `a ≥ 4`. -/
theorem uniform_size_real_bound : ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ, 4 ≤ a →
    (sizeCost a : ℝ) ≤ C * (Real.logb 2 a / Real.logb 2 (Real.logb 2 a)) := by
  obtain ⟨K,hK,hbound⟩ := uniform_size_input_bound
  refine ⟨4*K,by positivity,?_⟩
  intro a ha
  let x := Real.logb 2 a
  let n := Nat.clog 2 a
  let j := Nat.log 2 n
  have hapos : (0:ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hx : 2 ≤ x := by
    have hh := (Real.logb_le_logb (b := 2) (by norm_num) (by norm_num : (0:ℝ) < 4) hapos).mpr
      (show (4:ℝ) ≤ a from by exact_mod_cast ha)
    have he : Real.logb 2 (4:ℝ) = 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.logb_pow]
      norm_num
    simpa only [he] using hh
  have hxn : x ≤ (n:ℝ) := by
    have he : ⌈x⌉₊ = n := Real.natCeil_logb_natCast 2 a
    simpa only [he] using Nat.le_ceil x
  have hnx : (n:ℝ) ≤ 2*x := by
    have hh := Nat.ceil_lt_add_one (show (0:ℝ) ≤ x by linarith)
    rw [show ⌈x⌉₊ = n from Real.natCeil_logb_natCast 2 a] at hh
    linarith
  have hn : 2 ≤ n := by exact_mod_cast hx.trans hxn
  have hj : 1 ≤ j := Nat.log_pos (by omega) hn
  have hlogn : Real.logb 2 (n:ℝ) ≤ 2*j := by
    have hh := Nat.lt_floor_add_one (Real.logb 2 (n:ℝ))
    rw [show ⌊Real.logb 2 (n:ℝ)⌋₊ = Nat.log 2 n from Real.natFloor_logb_natCast 2 n] at hh
    have hj' : (1:ℝ) ≤ j := by exact_mod_cast hj
    dsimp [j] at *
    linarith
  have hlogx : Real.logb 2 x ≤ 2*j :=
    ((Real.logb_le_logb (by norm_num) (by linarith : (0:ℝ) < x)
      (by exact_mod_cast (show 0 < n by omega))).mpr hxn).trans hlogn
  have hpos : 0 < Real.logb 2 x := Real.logb_pos (by norm_num) (by linarith)
  have hmain : (sizeCost a:ℝ)*j ≤ (K:ℝ)*n := by exact_mod_cast hbound a
  have hK0 : (0:ℝ) ≤ K := by positivity
  have hG0 : (0:ℝ) ≤ sizeCost a := by positivity
  have htotal : (sizeCost a:ℝ)*Real.logb 2 x ≤ 4*(K:ℝ)*x := by
    calc (sizeCost a:ℝ)*Real.logb 2 x ≤ (sizeCost a:ℝ)*(2*j) := mul_le_mul_of_nonneg_left hlogx hG0
         _ = 2*((sizeCost a:ℝ)*j) := by ring
         _ ≤ 2*((K:ℝ)*n) := mul_le_mul_of_nonneg_left hmain (by norm_num)
         _ ≤ 2*((K:ℝ)*(2*x)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnx hK0) (by norm_num)
         _ = 4*(K:ℝ)*x := by ring
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hpos).mpr htotal

/-- Some `C > 0` satisfies `G a b ≤ C log₂ a / log₂ log₂ a` for all `b ≤ a` with `a ≥ 4`,
including non-coprime inputs. -/
theorem uniform_real_bound : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ, 4 ≤ a → b ≤ a →
    (G a b : ℝ) ≤ C * (Real.logb 2 a / Real.logb 2 (Real.logb 2 a)) := by
  obtain ⟨C,hC,hbound⟩ := uniform_size_real_bound
  refine ⟨C,hC,?_⟩
  intro a b ha hba
  exact (Nat.cast_le.mpr (G_le_sizeCost le_rfl hba)).trans (hbound a ha)

/-- `T̂(a) = O(log₂ a / log₂ log₂ a)`. -/
theorem sizeCost_isBigO :
    (fun a : ℕ => (sizeCost a : ℝ)) =O[Filter.atTop]
      (fun a => Real.logb 2 a / Real.logb 2 (Real.logb 2 a)) := by
  obtain ⟨C,hC,hbound⟩ := uniform_size_real_bound
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Filter.eventually_ge_atTop 4] with a ha
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs]
  exact (hbound a ha).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC.le)

/-- `T̂(a) = o(log₂ a)`: the worst case is strictly sublogarithmic. -/
theorem sizeCost_isLittleO_log :
    (fun a : ℕ => (sizeCost a : ℝ)) =o[Filter.atTop] (fun a => Real.logb 2 a) := by
  apply sizeCost_isBigO.trans_isLittleO
  apply (Asymptotics.isLittleO_iff_tendsto' (Filter.Eventually.of_forall (by
    intro a ha
    simp [ha]))).mpr
  have hlog : Filter.Tendsto (fun a : ℕ => Real.logb 2 (a:ℝ)) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hh := ((Real.tendsto_logb_atTop (by norm_num : (1:ℝ)<2)).comp hlog).inv_tendsto_atTop
  apply Filter.Tendsto.congr' _ hh
  filter_upwards [Filter.eventually_ge_atTop 2] with a ha
  have hp : 0 < Real.logb 2 (a:ℝ) := Real.logb_pos (by norm_num) (by exact_mod_cast (show 1<a by omega))
  dsimp
  field_simp

end ShortGCD
