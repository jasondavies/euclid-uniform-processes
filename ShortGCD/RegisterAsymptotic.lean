module

public import ShortGCD.RegisterRecurrence
public import ShortGCD.SharpBound

@[expose] public section

/-! # Fixed programs with arbitrarily small coefficients

For each `p > 0`, one generator of width `W = 4^p + 5` is fixed. Iterating `maxCost_step`
gives `limsup T_W(n)/n ≤ 3/p` (`Fixed.limsup_profile_le`), hence accepting runs with at most
`C log₂ a` remainder calls for every `C > 3/p` and large `a`. Taking `p > 3/ε` gives the
theorem of the paper's section "Fixed programs with arbitrarily small coefficients"
(`Fixed.arbitrarily_small_coefficient`); `RegisterSyntax` restates it for first-order
syntax.
-/

open Filter Topology
noncomputable section
namespace ShortGCD.RegisterProgram
namespace Fixed

/-- The prefix length `h = k² + 1`, with contraction ratio `k = 2^p`. -/
def prefixLength (p : ℕ) := (2^p)^2+1
/-- The width `W = h + 4`: `h + 1` prefix slots, the modulus, and two scratch residues. It
equals `4^p + 5` (`width_eq`). -/
def width (p : ℕ) := prefixLength p+4
/-- The number of contractions `J = ⌈n/p⌉`, so that `k^J ≥ 2^n`. -/
def steps (p n : ℕ) := Sharp.scale (1/(p:ℝ)) n
/-- The normalized cost `T_W(n)/n`, where `T_W(n) = maxCost W (2^n)`. -/
def profile (p n : ℕ) : ℝ := maxCost (width p) (2^n) / n

lemma width_eq (p : ℕ) : width p = 4^p+5 := by
  have he : (2^p)^2 = (4:ℕ)^p := by
    rw [← pow_mul, Nat.mul_comm p 2, pow_mul]
    norm_num
  simp [width, prefixLength, he]

lemma width_ge (p : ℕ) : 2 ≤ width p := by unfold width prefixLength; omega
lemma profile_nonneg (p n : ℕ) : 0 ≤ profile p n := by unfold profile; positivity
lemma profile_bounded (p : ℕ) : IsBoundedUnder (· ≤ ·) atTop (profile p) := by
  refine ⟨2, ?_⟩
  change ∀ᶠ n in atTop, profile p n ≤ 2
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h := maxCost_pow_le (width_ge p) n
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply (div_le_iff₀ hn0).mpr
  exact_mod_cast h

lemma profile_cobounded (p : ℕ) : IsCoboundedUnder (· ≤ ·) atTop (profile p) :=
  (show IsBoundedUnder (· ≥ ·) atTop (profile p) from
    ⟨0, (show ∀ᶠ n in atTop, 0 ≤ profile p n from Eventually.of_forall (profile_nonneg p))⟩).isCoboundedUnder_le

lemma recurrence {p : ℕ} (hp : 0 < p) {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ n : ℕ in atTop, maxCost (width p) (2^n) ≤
      max (prefixLength p+1+maxCost (width p) (2^(Sharp.scale (1-β/2) n)))
        (prefixLength p+3*steps p n+2+2*maxCost (width p) (2^(Sharp.scale β n))) := by
  have ht := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop (show 0 < β/2 by positivity)
  filter_upwards [ht.eventually (eventually_ge_atTop 1)] with n hn
  apply maxCost_step (hL := Nat.one_le_pow _ _ (by omega))
    (hh := by omega) (hk := Nat.one_le_pow _ _ (by omega))
    (hkh := Nat.lt_succ_self _)
  · have h1 := Nat.le_ceil ((1-β/2)*(n:ℝ))
    have h2 := Nat.le_ceil (β*(n:ℝ))
    have he : n+1 ≤ Sharp.scale β n + Sharp.scale (1-β/2) n := by
      change _ ≤ (Sharp.scale (1-β/2) n : ℝ) at h1
      change _ ≤ (Sharp.scale β n : ℝ) at h2
      have : (n:ℝ)+1 ≤ (Sharp.scale β n : ℝ) + (Sharp.scale (1-β/2) n : ℝ) := by linarith
      exact_mod_cast this
    calc 2*2^n = 2^(n+1) := by rw [pow_succ, Nat.mul_comm]
         _ ≤ 2^(Sharp.scale β n + Sharp.scale (1-β/2) n) := Nat.pow_le_pow_right (by omega) he
         _ = _ := pow_add _ _ _
  · have hp0 : (0:ℝ) < p := by exact_mod_cast hp
    have hj := Nat.le_ceil ((1/(p:ℝ)) * n)
    change _ ≤ (steps p n : ℝ) at hj
    have he : n ≤ p * steps p n := by
      have hh : (n:ℝ)/p ≤ steps p n := by simpa [div_eq_mul_inv, mul_comm] using hj
      have h := (div_le_iff₀ hp0).mp hh
      exact_mod_cast (by nlinarith : (n:ℝ) ≤ (p:ℝ)*steps p n)
    calc 2^n ≤ 2^(p*steps p n) := Nat.pow_le_pow_right (by omega) he
         _ = (2^p)^(steps p n) := pow_mul _ _ _
         _ ≤ _ := Nat.le_mul_of_pos_left _ (by positivity)

lemma constant_div_tendsto (c : ℝ) :
    Tendsto (fun n : ℕ => c/n) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

lemma early_limit (p : ℕ) : Tendsto (fun n : ℕ => ((prefixLength p:ℝ)+1)/n) atTop (𝓝 0) :=
  constant_div_tendsto _

lemma late_limit (p : ℕ) :
    Tendsto (fun n : ℕ => ((prefixLength p:ℝ)+3*steps p n+2)/n) atTop (𝓝 (3/(p:ℝ))) := by
  have h := (constant_div_tendsto ((prefixLength p:ℝ)+2)).add
    ((Sharp.scale_ratio (q := 1/(p:ℝ)) (by positivity)).const_mul 3)
  convert h using 1
  · funext n
    dsimp [steps]
    ring
  · congr 1
    ring

lemma cost_scale (p : ℕ) {q : ℝ} {n : ℕ} (hs : 0 < Sharp.scale q n) :
    (maxCost (width p) (2^(Sharp.scale q n)) : ℝ)/n =
      profile p (Sharp.scale q n) * ((Sharp.scale q n:ℝ)/n) := by
  have hs0 : (Sharp.scale q n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  dsimp [profile]
  field_simp

lemma limsup_recurrence {p : ℕ} (hp : 0 < p) {β : ℝ} (hβ0 : 0 < β) (hβ : β < 1/2) :
    limsup (profile p) atTop ≤ max ((1-β/2)*limsup (profile p) atTop)
      (2*β*limsup (profile p) atTop+3/(p:ℝ)) := by
  let L := limsup (profile p) atTop
  have hα : 0 < 1-β/2 := by linarith
  have hbound : ∀ u : ℝ, L < u → L ≤ max ((1-β/2)*u) (2*β*u+3/(p:ℝ)) := by
    intro u hu
    have hup := eventually_lt_of_limsup_lt hu (profile_bounded p)
    have hlim := ((early_limit p).add ((Sharp.scale_ratio hα.le).const_mul u)).max
      ((late_limit p).add ((Sharp.scale_ratio hβ0.le).const_mul (2*u)))
    have hle : ∀ᶠ n : ℕ in atTop, profile p n ≤
        max (((prefixLength p:ℝ)+1)/n + u*((Sharp.scale (1-β/2) n:ℝ)/n))
          (((prefixLength p:ℝ)+3*steps p n+2)/n + (2*u)*((Sharp.scale β n:ℝ)/n)) := by
      filter_upwards [recurrence hp hβ0, eventually_ge_atTop 1,
        (Sharp.scale_tendsto hα).eventually (eventually_ge_atTop 1),
        (Sharp.scale_tendsto hβ0).eventually (eventually_ge_atTop 1),
        (Sharp.scale_tendsto hα).eventually hup, (Sharp.scale_tendsto hβ0).eventually hup]
        with n hr hn hsa hsb hua hub
      have hr' : (maxCost (width p) (2^n):ℝ) ≤
        max ((prefixLength p:ℝ)+1+maxCost (width p) (2^(Sharp.scale (1-β/2) n)))
          ((prefixLength p:ℝ)+3*steps p n+2+2*maxCost (width p) (2^(Sharp.scale β n))) := by
        exact_mod_cast hr
      have hd := div_le_div_of_nonneg_right hr' (Nat.cast_nonneg n)
      rw [← max_div_div_right (by positivity : (0:ℝ) ≤ n)] at hd
      apply hd.trans
      apply max_le_max
      · rw [add_div, cost_scale p (by omega : 0 < Sharp.scale (1-β/2) n)]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hua.le (by positivity))
      · have hcost := cost_scale p (by omega : 0 < Sharp.scale β n)
        have hmul := mul_le_mul_of_nonneg_right hub.le
          (show 0 ≤ (Sharp.scale β n:ℝ)/(n:ℝ) by positivity)
        rw [add_div, mul_div_assoc, hcost]
        nlinarith
    have hh := limsup_le_limsup hle (profile_cobounded p) hlim.isBoundedUnder_le
    rw [hlim.limsup_eq] at hh
    convert hh using 1
    congr 1 <;> ring
  have hlim : Tendsto (fun u : ℝ => max ((1-β/2)*u) (2*β*u+3/(p:ℝ)))
      (𝓝[>] L) (𝓝 (max ((1-β/2)*L) (2*β*L+3/(p:ℝ)))) := by
    exact (show ContinuousAt (fun u : ℝ => max ((1-β/2)*u) (2*β*u+3/(p:ℝ))) L by
      fun_prop).tendsto.mono_left inf_le_left
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact hbound u hu

/-- For each `p > 0`, the fixed generator of width `W = 4^p + 5` satisfies
`limsup_{n → ∞} T_W(n)/n ≤ 3/p`, where `T_W(n) = maxCost W (2^n)`. -/
theorem limsup_profile_le {p : ℕ} (hp : 0 < p) : limsup (profile p) atTop ≤ 3/(p:ℝ) := by
  have hnonneg : 0 ≤ limsup (profile p) atTop := by
    apply le_limsup_of_le (profile_bounded p)
    intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact (profile_nonneg p n).trans hn
  have hparameter : ∀ β : ℝ, 0 < β → β < 1/2 →
      limsup (profile p) atTop * (1-2*β) ≤ 3/(p:ℝ) := by
    intro β hβ0 hβ
    have h := limsup_recurrence hp hβ0 hβ
    have hpos : 0 < 3/(p:ℝ) := by positivity
    rcases le_max_iff.mp h with h | h
    · have : limsup (profile p) atTop = 0 := by nlinarith
      rw [this, zero_mul]; exact hpos.le
    · nlinarith
  have hlim : Tendsto (fun β : ℝ => limsup (profile p) atTop * (1-2*β))
      (𝓝[>] 0) (𝓝 (limsup (profile p) atTop)) := by
    simpa using (show ContinuousAt (fun β : ℝ => limsup (profile p) atTop * (1-2*β)) 0 by
      fun_prop).tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from inf_le_left)
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0:ℝ) < 1/2 by norm_num)).filter_mono inf_le_left] with β hβ0 hβ
  exact hparameter β hβ0 hβ

lemma accepts_cost {w a b} (hw : 2 ≤ w) :
    ∃ n, Accepts w a b n (Nat.gcd a b) ∧ n ≤ cost w a b+2 := by
  by_cases hb : b = 0
  · subst b
    exact ⟨0, by simpa using Accepts.zero (width := w) a, by omega⟩
  obtain ⟨n, hn, hr⟩ := computes_cost hw a b
  refine ⟨n+2, .checked (by omega) hr (Nat.gcd_pos_of_pos_right a (by omega))
    (Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left a b))
    (Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right a b)), by omega⟩

lemma input_ratio : Tendsto (fun a : ℕ => (Nat.clog 2 a:ℝ)/Real.logb 2 a)
    atTop (𝓝 1) := by
  have h := (tendsto_nat_ceil_div_atTop (R := ℝ)).comp Sharp.log_tendsto
  simpa only [Function.comp_def, Sharp.ceil_log_nat] using h

/-- For `p > 0` and `C > 3/p`: for all sufficiently large `a` and every `b ≤ a`, the program of
width `4^p + 5` has an accepting run on `(a, b)` returning `gcd(a, b)` with at most `C log₂ a`
remainder calls, counting the two verification calls. -/
theorem eventually_accepts_bound {p : ℕ} (hp : 0 < p) {C : ℝ} (hC : 3/(p:ℝ) < C) :
    ∀ᶠ a : ℕ in atTop, ∀ b, b ≤ a → ∃ n,
      Accepts (width p) a b n (Nat.gcd a b) ∧ (n:ℝ) ≤ C*Real.logb 2 a := by
  obtain ⟨u, hu, huC⟩ := exists_between hC
  have hprof := eventually_lt_of_limsup_lt ((limsup_profile_le hp).trans_lt hu) (profile_bounded p)
  have hclog : Tendsto (Nat.clog 2) atTop atTop := by
    simpa only [Function.comp_def, Sharp.ceil_log_nat] using tendsto_nat_ceil_atTop.comp Sharp.log_tendsto
  have hlim : Tendsto (fun a : ℕ => u*((Nat.clog 2 a:ℝ)/Real.logb 2 a)+2/Real.logb 2 a)
      atTop (𝓝 u) := by
    simpa using (input_ratio.const_mul u).add (tendsto_const_nhds.div_atTop Sharp.log_tendsto)
  filter_upwards [eventually_ge_atTop 2, hclog.eventually hprof,
    hclog.eventually (eventually_ge_atTop 1), (tendsto_order.mp hlim).2 C huC]
    with a ha hpa hca henv
  intro b hb
  obtain ⟨n, hn, hnc⟩ := accepts_cost (a := a) (b := b) (width_ge p)
  refine ⟨n, hn, ?_⟩
  have ha2 : a ≤ 2^(Nat.clog 2 a) := Nat.le_pow_clog (by omega) a
  have hcost := cost_le_maxCost (w := width p) ha2 (hb.trans ha2)
  have hlog : 0 < Real.logb 2 (a:ℝ) := Real.logb_pos (by norm_num) (by exact_mod_cast ha)
  have hcp : (0:ℝ) < Nat.clog 2 a := by exact_mod_cast (show 0 < Nat.clog 2 a by omega)
  have hprof' : (maxCost (width p) (2^Nat.clog 2 a):ℝ) < u*Nat.clog 2 a :=
    (div_lt_iff₀ hcp).mp hpa
  have hnc' : (n:ℝ) ≤ (maxCost (width p) (2^Nat.clog 2 a):ℝ)+2 := by
    exact_mod_cast hnc.trans (Nat.add_le_add_right hcost 2)
  have he : u*(Nat.clog 2 a:ℝ)+2 < C*Real.logb 2 a := by
    have h := (div_lt_iff₀ hlog).mp
      (show (u*(Nat.clog 2 a:ℝ)+2)/Real.logb 2 a < C by
        simpa only [add_div, mul_div_assoc] using henv)
    exact h
  linarith

/-- **Fixed programs with arbitrarily small coefficients.** For every `ε > 0` there are `p > 0`
and `B ≥ 0` such that, for all `1 ≤ b ≤ a`, the program of width `4^p + 5` has an accepting run
on `(a, b)` returning `gcd(a, b)` with at most `ε log₂ a + B` remainder calls. The program
depends on `ε` and `B` covers small inputs; this is not a single sublogarithmic program. -/
theorem arbitrarily_small_coefficient {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℕ, 0 < p ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℕ, 1 ≤ b → b ≤ a →
      ∃ n, Accepts (width p) a b n (Nat.gcd a b) ∧ (n:ℝ) ≤ ε*Real.logb 2 a+B := by
  obtain ⟨p, hp⟩ := exists_nat_gt (3/ε)
  have hp0 : 0 < p := by
    have : (0:ℝ) < p := lt_trans (by positivity : 0 < 3/ε) hp
    exact_mod_cast this
  have hcoef : 3/(p:ℝ) < ε := by
    apply (div_lt_iff₀ (by exact_mod_cast hp0)).mpr
    have h := (div_lt_iff₀ hε).mp hp
    nlinarith
  obtain ⟨A, hA⟩ := eventually_atTop.mp (eventually_accepts_bound hp0 hcoef)
  refine ⟨p, hp0, maxCost (width p) A+2, by positivity, ?_⟩
  intro a b hb hab
  by_cases ha : A ≤ a
  · obtain ⟨n, hn, hc⟩ := hA a ha b hab
    refine ⟨n, hn, ?_⟩
    have : (0:ℝ) ≤ maxCost (width p) A := by positivity
    linarith
  · obtain ⟨n, hn, hc⟩ := accepts_cost (a := a) (b := b) (width_ge p)
    have hm := cost_le_maxCost (w := width p) (show a ≤ A by omega) (show b ≤ A by omega)
    have hc' : (n:ℝ) ≤ (maxCost (width p) A:ℝ)+2 := by
      exact_mod_cast hc.trans (Nat.add_le_add_right hm 2)
    have hl : 0 ≤ Real.logb 2 (a:ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ a by omega))
    exact ⟨n, hn, by nlinarith⟩

end Fixed
end ShortGCD.RegisterProgram
