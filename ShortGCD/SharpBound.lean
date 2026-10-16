import ShortGCD.Asymptotic

/-! # The leading constant in the uniform bound

The finite construction is reused with a prefix of size roughly `n^(2*c)`,
where `0 < c < 1/2`, and arbitrarily small fixed recursive size ratios.
The original Big-O theorem supplies boundedness before taking upper limits.
-/

open Filter Topology

noncomputable section
namespace ShortGCD
namespace Sharp

def weight (n : ℕ) : ℝ := Real.logb 2 n / n
def profile (n : ℕ) : ℝ := sizeCost (2^n) * weight n
def scale (q : ℝ) (n : ℕ) : ℕ := ⌈q * n⌉₊
def exponent (c : ℝ) (n : ℕ) : ℕ := ⌊c * Real.logb 2 n⌋₊
def prefixSize (c : ℝ) (n : ℕ) : ℕ := (2^(exponent c n))^2 + 1
def steps (c : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) / exponent c n⌉₊

lemma log_tendsto : Tendsto (fun n : ℕ => Real.logb 2 n) atTop atTop :=
  (Real.tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop

lemma weight_nonneg (n : ℕ) : 0 ≤ weight n := by
  rcases n with _ | n
  · simp [weight]
  · exact div_nonneg (Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.succ_pos n))
      (Nat.cast_nonneg _)

lemma weight_tendsto : Tendsto weight atTop (𝓝 0) :=
  Real.isLittleO_logb_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

lemma profile_nonneg (n : ℕ) : 0 ≤ profile n :=
  mul_nonneg (Nat.cast_nonneg _) (weight_nonneg n)

lemma profile_bounded : IsBoundedUnder (· ≤ ·) atTop profile := by
  obtain ⟨C, _, hC⟩ := uniform_size_real_bound
  refine ⟨C, ?_⟩
  change ∀ᶠ n in atTop, profile n ≤ C
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hl : 0 < Real.logb 2 (n : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < n by omega))
  have h := hC (2^n) (by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hn)
  have he : Real.logb 2 ((2^n : ℕ) : ℝ) = n := by
    push_cast
    rw [Real.logb_pow]
    norm_num
  rw [he] at h
  have hh := mul_le_mul_of_nonneg_right h (weight_nonneg n)
  convert hh using 1 <;> dsimp [profile, weight]
  field_simp

lemma profile_cobounded : IsCoboundedUnder (· ≤ ·) atTop profile :=
  (show IsBoundedUnder (· ≥ ·) atTop profile from
    ⟨0, (show ∀ᶠ n in atTop, 0 ≤ profile n from Eventually.of_forall profile_nonneg)⟩).isCoboundedUnder_le

lemma scale_tendsto {q : ℝ} (hq : 0 < q) : Tendsto (scale q) atTop atTop :=
  tendsto_nat_ceil_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hq)

lemma scale_ratio {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun n : ℕ => (scale q n : ℝ) / n) atTop (𝓝 q) :=
  (tendsto_nat_ceil_mul_div_atTop hq).comp tendsto_natCast_atTop_atTop

/-- Logarithms of linearly rescaled, rounded arguments have asymptotic ratio one. -/
lemma scale_log_ratio {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n : ℕ => Real.logb 2 (scale q n) / Real.logb 2 n) atTop (𝓝 1) := by
  have h := ((scale_ratio hq.le).logb (by positivity : q ≠ 0) (b := 2)).div_atTop log_tendsto
  have hh := h.const_add 1
  have heq : (fun n : ℕ => (1 : ℝ) + Real.logb 2 ((scale q n : ℝ) / n) /
      Real.logb 2 n) =ᶠ[atTop]
      (fun n : ℕ => Real.logb 2 (scale q n) / Real.logb 2 n) := by
    filter_upwards [eventually_ge_atTop 2, (scale_tendsto hq).eventually (eventually_ge_atTop 1)] with n hn hs
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hs0 : (scale q n : ℝ) ≠ 0 := by exact_mod_cast (show scale q n ≠ 0 by omega)
    have hl : Real.logb 2 (n : ℝ) ≠ 0 := ne_of_gt
      (Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < n by omega)))
    rw [Real.logb_div hs0 hn0]
    field_simp
    ring
  exact (by simpa using hh : Tendsto _ atTop (𝓝 (1 : ℝ))).congr' heq

/-- Factor converting the normalized cost at a recursive argument to the current scale. -/
def factor (q : ℝ) (n : ℕ) : ℝ :=
  (scale q n : ℝ) / n * (Real.logb 2 n / Real.logb 2 (scale q n))

lemma factor_tendsto {q : ℝ} (hq : 0 < q) :
    Tendsto (factor q) atTop (𝓝 q) := by
  have h := (scale_ratio hq.le).mul ((scale_log_ratio hq).inv₀ (by norm_num))
  change Tendsto (fun n => (scale q n : ℝ) / n * (Real.logb 2 n / Real.logb 2 (scale q n))) atTop (𝓝 q)
  simpa only [inv_div, inv_one, mul_one] using h

lemma cost_scale {q : ℝ} {n : ℕ} (hn : 2 ≤ n) (hs : 2 ≤ scale q n) :
    (sizeCost (2^(scale q n)) : ℝ) * weight n = profile (scale q n) * factor q n := by
  have hs0 : (scale q n : ℝ) ≠ 0 := by exact_mod_cast (show scale q n ≠ 0 by omega)
  have hl : Real.logb 2 (scale q n : ℝ) ≠ 0 := ne_of_gt
    (Real.logb_pos (by norm_num) (by exact_mod_cast (show 1 < scale q n by omega)))
  dsimp [profile, factor, weight]
  field_simp

lemma exponent_tendsto {c : ℝ} (hc : 0 < c) : Tendsto (exponent c) atTop atTop :=
  tendsto_nat_floor_atTop.comp (log_tendsto.const_mul_atTop hc)

lemma exponent_ratio {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => (exponent c n : ℝ) / Real.logb 2 n) atTop (𝓝 c) :=
  (tendsto_nat_floor_mul_div_atTop hc).comp log_tendsto

lemma prefixSize_le {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 2 ≤ n) :
    (prefixSize c n : ℝ) ≤ (n : ℝ) ^ (2*c) + 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))
  have hp := Nat.floor_le (mul_nonneg hc hl)
  change (exponent c n : ℝ) ≤ c * Real.logb 2 n at hp
  have he : (2 : ℝ) ^ ((2 : ℝ) * exponent c n) ≤ (n : ℝ) ^ (2*c) := by
    calc
      _ ≤ (2 : ℝ) ^ (Real.logb 2 n * (2*c)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ = _ := by rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn0]
  have he' : ((2 : ℝ) ^ exponent c n)^2 ≤ (n : ℝ) ^ (2*c) := by
    convert he using 1
    rw [mul_comm (2 : ℝ), Real.rpow_mul (by norm_num), Real.rpow_natCast, Real.rpow_two]
  simpa [prefixSize] using add_le_add_right he' 1

lemma power_weight_tendsto {c : ℝ} (hc : c < 1/2) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (2*c) * weight n) atTop (𝓝 0) := by
  have hpow := (isLittleO_log_rpow_atTop (r := 1-2*c) (by linarith)).tendsto_div_nhds_zero
  have h := (hpow.div_const (Real.log 2)).comp tendsto_natCast_atTop_atTop
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp [weight, Real.logb]
  rw [Real.rpow_sub hn0, Real.rpow_one]
  field_simp

lemma early_overhead_tendsto {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1/2) :
    Tendsto (fun n : ℕ => ((prefixSize c n : ℝ)+1) * weight n) atTop (𝓝 0) := by
  have h := (power_weight_tendsto hc).add (weight_tendsto.const_mul 2)
  simp only [mul_zero, add_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · exact Eventually.of_forall (fun n => mul_nonneg (by positivity) (weight_nonneg n))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hp := prefixSize_le hc0 hn
    have hh := mul_le_mul_of_nonneg_right (show (prefixSize c n : ℝ)+1 ≤ (n:ℝ)^(2*c)+2 by linarith)
      (weight_nonneg n)
    nlinarith

lemma steps_weight_upper (c : ℝ) (n : ℕ) :
    (steps c n : ℝ) * weight n ≤ Real.logb 2 n / exponent c n + weight n := by
  have hs := (Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) / exponent c n by positivity)).le
  change (steps c n : ℝ) ≤ (n : ℝ) / exponent c n + 1 at hs
  have hh := mul_le_mul_of_nonneg_right hs (weight_nonneg n)
  rcases n with _ | n
  · simp [weight]
  · have hn0 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    convert hh using 1
    dsimp [weight]
    field_simp

/-- A convergent upper envelope for the large-branch overhead. -/
def lateEnvelope (c : ℝ) (n : ℕ) : ℝ :=
  ((prefixSize c n : ℝ)+1) * weight n +
    3 * (Real.logb 2 n / exponent c n) + 4 * weight n

lemma lateEnvelope_tendsto {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) :
    Tendsto (lateEnvelope c) atTop (𝓝 (3/c)) := by
  have h := ((early_overhead_tendsto hc0.le hc).add
    (((exponent_ratio hc0.le).inv₀ hc0.ne').const_mul 3)).add (weight_tendsto.const_mul 4)
  change Tendsto (fun n => ((prefixSize c n : ℝ)+1) * weight n +
    3 * (Real.logb 2 n / exponent c n) + 4 * weight n) atTop (𝓝 (3/c))
  simpa [inv_div, div_eq_mul_inv] using h

lemma late_overhead_le (c : ℝ) (n : ℕ) :
    ((prefixSize c n : ℝ) + 3 * steps c n + 2) * weight n ≤ lateEnvelope c n := by
  have h := steps_weight_upper c n
  dsimp [lateEnvelope]
  nlinarith

/-- The finite construction with tunable real parameters, rounded to natural numbers. -/
lemma recurrence {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    ∀ᶠ n : ℕ in atTop, sizeCost (2^n) ≤
      max (prefixSize c n+1+sizeCost (2^(scale (1-β/2) n)))
        (prefixSize c n+3*steps c n+2+2*sizeCost (2^(scale β n))) := by
  have hthreshold := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop (show 0 < β/2 by positivity)
  filter_upwards [(exponent_tendsto hc).eventually (eventually_ge_atTop 1),
    hthreshold.eventually (eventually_ge_atTop 1)] with n hp hn
  apply sizeCost_step (hL := Nat.one_le_pow _ _ (by omega))
    (hh := by positivity) (hk := Nat.one_le_pow _ _ (by omega))
    (hkh := Nat.lt_succ_self _)
  · have h1 := Nat.le_ceil ((1-β/2)*(n:ℝ))
    have h2 := Nat.le_ceil (β*(n:ℝ))
    have he : n+1 ≤ scale β n + scale (1-β/2) n := by
      change _ ≤ (scale (1-β/2) n : ℝ) at h1
      change _ ≤ (scale β n : ℝ) at h2
      have : (n:ℝ)+1 ≤ (scale β n : ℝ) + (scale (1-β/2) n : ℝ) := by linarith
      exact_mod_cast this
    calc 2*2^n = 2^(n+1) := by rw [pow_succ, Nat.mul_comm]
         _ ≤ 2^(scale β n + scale (1-β/2) n) := Nat.pow_le_pow_right (by omega) he
         _ = _ := pow_add _ _ _
  · have hp0 : (0 : ℝ) < exponent c n := by exact_mod_cast hp
    have hj := Nat.le_ceil ((n : ℝ) / exponent c n)
    change _ ≤ (steps c n : ℝ) at hj
    have he : n ≤ exponent c n * steps c n := by
      have := (div_le_iff₀ hp0).mp hj
      exact_mod_cast (by nlinarith : (n:ℝ) ≤ (exponent c n : ℝ) * (steps c n : ℝ))
    calc 2^n ≤ 2^(exponent c n * steps c n) := Nat.pow_le_pow_right (by omega) he
         _ = (2^exponent c n)^(steps c n) := pow_mul _ _ _
         _ ≤ _ := Nat.le_mul_of_pos_left _ (by positivity)

lemma factor_nonneg {q : ℝ} {n : ℕ} (hn : 2 ≤ n) (hs : 2 ≤ scale q n) :
    0 ≤ factor q n := by
  have hl : 0 ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))
  have hs' : 0 ≤ Real.logb 2 (scale q n : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ scale q n by omega))
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (div_nonneg hl hs')

lemma limsup_recurrence {c β : ℝ} (hc0 : 0 < c) (hc : c < 1/2)
    (hβ0 : 0 < β) (hβ : β < 1/2) :
    limsup profile atTop ≤ max ((1-β/2) * limsup profile atTop)
      (2*β * limsup profile atTop + 3/c) := by
  let L := limsup profile atTop
  have hα : 0 < 1-β/2 := by linarith
  have hbound : ∀ u : ℝ, L < u → L ≤ max ((1-β/2)*u) (2*β*u+3/c) := by
    intro u hu
    have hup := eventually_lt_of_limsup_lt hu profile_bounded
    have hlim := ((early_overhead_tendsto hc0.le hc).add ((factor_tendsto hα).const_mul u)).max
      ((lateEnvelope_tendsto hc0 hc).add ((factor_tendsto hβ0).const_mul (2*u)))
    have hle : ∀ᶠ n : ℕ in atTop, profile n ≤
        max (((prefixSize c n : ℝ)+1)*weight n + u*factor (1-β/2) n)
          (lateEnvelope c n + (2*u)*factor β n) := by
      filter_upwards [recurrence hc0 hβ0, eventually_ge_atTop 2,
        (scale_tendsto hα).eventually (eventually_ge_atTop 2),
        (scale_tendsto hβ0).eventually (eventually_ge_atTop 2),
        (scale_tendsto hα).eventually hup, (scale_tendsto hβ0).eventually hup]
        with n hr hn hsa hsb hua hub
      have hr' : (sizeCost (2^n) : ℝ) ≤
          max ((prefixSize c n : ℝ)+1+sizeCost (2^(scale (1-β/2) n)))
            ((prefixSize c n : ℝ)+3*steps c n+2+2*sizeCost (2^(scale β n))) := by
        exact_mod_cast hr
      have hh := mul_le_mul_of_nonneg_right hr' (weight_nonneg n)
      rw [max_mul_of_nonneg _ _ (weight_nonneg n)] at hh
      apply hh.trans
      apply max_le_max
      · rw [add_mul, cost_scale hn hsa]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hua.le (factor_nonneg hn hsa))
      · have hcost := cost_scale hn hsb
        have hmul := mul_le_mul_of_nonneg_right hub.le (factor_nonneg hn hsb)
        have ho := late_overhead_le c n
        nlinarith
    have hh := limsup_le_limsup hle profile_cobounded hlim.isBoundedUnder_le
    rw [hlim.limsup_eq] at hh
    convert hh using 1
    congr 1 <;> ring
  have hlim : Tendsto (fun u : ℝ => max ((1-β/2)*u) (2*β*u+3/c))
      (𝓝[>] L) (𝓝 (max ((1-β/2)*L) (2*β*L+3/c))) := by
    exact (show ContinuousAt (fun u : ℝ => max ((1-β/2)*u) (2*β*u+3/c)) L by
      fun_prop).tendsto.mono_left inf_le_left
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact hbound u hu

lemma limsup_nonneg : 0 ≤ limsup profile atTop := by
  apply le_limsup_of_le profile_bounded
  intro b hb
  obtain ⟨n, hn⟩ := hb.exists
  exact (profile_nonneg n).trans hn

lemma limsup_parameter_bound {c β : ℝ} (hc0 : 0 < c) (hc : c < 1/2)
    (hβ0 : 0 < β) (hβ : β < 1/2) :
    limsup profile atTop * (1-2*β) ≤ 3/c := by
  have h := limsup_recurrence hc0 hc hβ0 hβ
  have hL := limsup_nonneg
  have hpos : 0 < 3/c := by positivity
  rcases le_max_iff.mp h with h | h
  · have : limsup profile atTop = 0 := by nlinarith
    rw [this, zero_mul]
    exact hpos.le
  · nlinarith

lemma limsup_le_three_div {c : ℝ} (hc0 : 0 < c) (hc : c < 1/2) :
    limsup profile atTop ≤ 3/c := by
  have hlim : Tendsto (fun β : ℝ => limsup profile atTop * (1-2*β))
      (𝓝[>] 0) (𝓝 (limsup profile atTop)) := by
    simpa using (show ContinuousAt (fun β : ℝ => limsup profile atTop * (1-2*β)) 0 by
      fun_prop).tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1/2 by norm_num)).filter_mono inf_le_left] with β hβ0 hβ
  exact limsup_parameter_bound hc0 hc hβ0 hβ

/-- The normalized worst-case bit complexity has upper limit at most six. -/
theorem limsup_profile_le_six : limsup profile atTop ≤ 6 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc0 : 0 < 3/(6+ε) := by positivity
  have hc : 3/(6+ε) < (1 : ℝ)/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 6+ε)).mpr
    linarith
  have h := limsup_le_three_div hc0 hc
  have he : (3 : ℝ)/(3/(6+ε)) = 6+ε := by field_simp
  rwa [he] at h

/-- Every constant strictly greater than six eventually bounds the bit profile. -/
theorem eventually_profile_lt {C : ℝ} (hC : 6 < C) :
    ∀ᶠ n in atTop, profile n < C :=
  eventually_lt_of_limsup_lt (limsup_profile_le_six.trans_lt hC) profile_bounded

lemma ceil_log_ratio : Tendsto (fun x : ℝ => Real.logb 2 ⌈x⌉₊ / Real.logb 2 x)
    atTop (𝓝 1) := by
  have he := (Asymptotics.isEquivalent_nat_ceil (R := ℝ)).log tendsto_id
  have hn : ∀ᶠ x : ℝ in atTop, Real.log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact (Real.log_pos hx).ne'
  have h := (Asymptotics.isEquivalent_iff_tendsto_one hn).mp he
  change Tendsto (fun x : ℝ => Real.log (⌈x⌉₊ : ℝ) / Real.log x) atTop (𝓝 1) at h
  simpa only [Pi.div_apply, Real.logb, div_div_div_cancel_right₀ (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'] using h

lemma ceil_log_nat (a : ℕ) : ⌈Real.logb 2 (a : ℝ)⌉₊ = Nat.clog 2 a :=
  Real.natCeil_logb_natCast 2 a

def inputFactor (a : ℕ) : ℝ :=
  (Nat.clog 2 a : ℝ) / Real.logb 2 a *
    (Real.logb 2 (Real.logb 2 a) / Real.logb 2 (Nat.clog 2 a))

def inputWeight (a : ℕ) : ℝ := Real.logb 2 (Real.logb 2 a) / Real.logb 2 a

lemma inputFactor_tendsto : Tendsto inputFactor atTop (𝓝 1) := by
  have h := (tendsto_nat_ceil_div_atTop (R := ℝ)).mul (ceil_log_ratio.inv₀ (by norm_num))
  have hh := h.comp log_tendsto
  change Tendsto (fun a : ℕ => (Nat.clog 2 a : ℝ) / Real.logb 2 a *
    (Real.logb 2 (Real.logb 2 a) / Real.logb 2 (Nat.clog 2 a))) atTop (𝓝 1)
  simpa only [Function.comp_def, inv_div, inv_one, mul_one, ceil_log_nat] using hh

lemma inputWeight_tendsto : Tendsto inputWeight atTop (𝓝 0) :=
  Real.isLittleO_logb_id_atTop.tendsto_div_nhds_zero.comp log_tendsto

lemma clog_tendsto : Tendsto (Nat.clog 2) atTop atTop := by
  simpa only [Function.comp_def, ceil_log_nat] using tendsto_nat_ceil_atTop.comp log_tendsto

lemma input_parameters {a : ℕ} (ha : 4 ≤ a) :
    0 < Real.logb 2 a ∧ 0 < Real.logb 2 (Real.logb 2 a) ∧
    0 < (Nat.clog 2 a : ℝ) ∧ 0 < Real.logb 2 (Nat.clog 2 a) := by
  have hloga : 2 ≤ Real.logb 2 (a : ℝ) := by
    have h := Real.logb_le_logb (b := 2) (by norm_num) (by norm_num : (0:ℝ)<4)
      (show (0 : ℝ) < (a : ℝ) from by exact_mod_cast (show 0 < a by omega))
    have hh := h.mpr (show (4:ℝ) ≤ a by exact_mod_cast ha)
    have he : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.logb_pow]
      norm_num
    simpa only [he] using hh
  have hceil := Nat.le_ceil (Real.logb 2 (a : ℝ))
  rw [ceil_log_nat] at hceil
  exact ⟨by linarith, Real.logb_pos (by norm_num) (by linarith), by linarith,
    Real.logb_pos (by norm_num) (by linarith)⟩

lemma sizeCost_input_le {a : ℕ} (ha : 4 ≤ a) :
    (sizeCost a : ℝ) * inputWeight a ≤ profile (Nat.clog 2 a) * inputFactor a := by
  obtain ⟨hx, hy, hn, hl⟩ := input_parameters ha
  have hmono : sizeCost a ≤ sizeCost (2^(Nat.clog 2 a)) := by
    apply sizeCost_le
    intro x y hxa hya
    exact sizeCost_bound _ x y (hxa.trans (Nat.le_pow_clog (by omega) a))
      (hya.trans (Nat.le_pow_clog (by omega) a))
  have h := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmono)
    (show 0 ≤ inputWeight a from (div_pos hy hx).le)
  convert h using 1
  dsimp [profile, weight, inputWeight, inputFactor]
  field_simp

end Sharp

/-- The leading constant six is uniform over input size. Any fixed number of
additional instructions is absorbed without changing that leading constant. -/
theorem eventually_sizeCost_add_le_six (K : ℕ) {C : ℝ} (hC : 6 < C) :
    ∀ᶠ a : ℕ in atTop, (sizeCost a + K : ℝ) ≤
      C * (Real.logb 2 a / Real.logb 2 (Real.logb 2 a)) := by
  let B := (6+C)/2
  have hB : 6 < B := by dsimp [B]; linarith
  have hBC : B < C := by dsimp [B]; linarith
  have hlim := (Sharp.inputFactor_tendsto.const_mul B).add
    (Sharp.inputWeight_tendsto.const_mul (K : ℝ))
  simp only [mul_one, mul_zero, add_zero] at hlim
  filter_upwards [Sharp.clog_tendsto.eventually (Sharp.eventually_profile_lt hB),
    hlim.eventually_lt_const hBC, eventually_ge_atTop 4] with a ha hlim ha4
  obtain ⟨hx, hy, hn, hl⟩ := Sharp.input_parameters ha4
  have hfac : 0 ≤ Sharp.inputFactor a :=
    mul_nonneg (div_nonneg hn.le hx.le) (div_nonneg hy.le hl.le)
  have hbound := (Sharp.sizeCost_input_le ha4).trans
    (mul_le_mul_of_nonneg_right ha.le hfac)
  have hh : ((sizeCost a : ℝ) + K) * Sharp.inputWeight a ≤ C := by nlinarith
  dsimp [Sharp.inputWeight] at hh
  apply (le_div_iff₀ (div_pos hy hx)).mpr at hh
  convert hh using 1
  field_simp

/-- For every ε > 0, all sufficiently large inputs satisfy the bound with
coefficient `6 + ε`. The threshold is independent of the second input. -/
theorem uniform_real_bound_six {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℕ in atTop, ∀ b : ℕ, b ≤ a →
      (G a b : ℝ) ≤ (6+ε) * (Real.logb 2 a / Real.logb 2 (Real.logb 2 a)) := by
  filter_upwards [eventually_sizeCost_add_le_six 0 (show 6 < 6+ε by linarith)] with a ha
  intro b hba
  exact (Nat.cast_le.mpr (G_le_sizeCost le_rfl hba)).trans (by simpa using ha)

end ShortGCD
