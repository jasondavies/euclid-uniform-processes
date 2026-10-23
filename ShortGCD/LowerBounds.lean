module

public import ShortGCD.Conjecture
public import ShortGCD.AlmostAll

@[expose] public section

/-!
# Lower bounds for the intrinsic complexities

These statements show that the intrinsic complexities refuted in `ShortGCD.Conjecture` are not
small for trivial reasons:

* `exists_certifiesCoprimeness`, `exists_certifiesGcd`: certificates exist, so each complexity
  is the size of an actual certificate, not `sInf ∅ = 0`.
* `G_le_callsRemGcd`, `G_le_callsGcd`: every gcd certificate needs at least `G a b` remainder
  facts, so both gcd complexities are at least `G a b`.
* `callsCoprimeness_eq_G`: on positive coprime inputs the complexity of the book's coprimeness
  relation is exactly `G a b`.
* `tendsto_card_callsCoprimeness_loglog`: the coprimeness complexity is at least
  `(1 − ε) log₂ log₂ N` on all but `o(N²)` coprime pairs `2 ≤ b < a ≤ N`.
-/

open Filter Topology

namespace ShortGCD

/-- For `a, b ≥ 1`, some certificate settles the truth value of `a ⊥⊥ b`, so
`callsCoprimeness a b` is the size of an actual certificate, not `sInf ∅ = 0`. -/
theorem exists_certifiesCoprimeness {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ U : Cert, CertifiesCoprimeness U a b := by
  by_cases hc : Nat.Coprime a b
  · obtain ⟨U, hU, -⟩ := coprime_certificate_bound hc
    exact ⟨_, certifiesCoprimeness_of_certifiesCoprime ha hb hU⟩
  · obtain ⟨U, hS, hG, -, hπ⟩ := noncoprime_certificate_bound ha hc
    exact ⟨U, hS, hG, fun π h ↦ iff_of_false (fun h' ↦ hπ π h h'.2.2) fun h' ↦ hc h'.2.2⟩

/-- Every pair has a gcd certificate without `eq1` facts, so `callsGcd a b` and
`callsRemGcd a b` are sizes of actual certificates, not `sInf ∅ = 0`. -/
theorem exists_certifiesGcd (a b : ℕ) : ∃ U : Cert, U.CertifiesGcd a b ∧ U.eq1s = ∅ := by
  obtain ⟨-, U, hU, h1, -⟩ := callsGcd_set_nonempty a b
  exact ⟨U, hU, h1⟩

/-- Every pair has a gcd certificate in `Nε`, so `callsRemGcd` is a minimum, not `sInf ∅`. -/
theorem callsRemGcd_set_nonempty' (a b : ℕ) :
    {k | ∃ U : Cert, U.CertifiesGcd a b ∧ U.rems.card = k}.Nonempty := by
  obtain ⟨k, U, hU, -, hk⟩ := callsGcd_set_nonempty a b
  exact ⟨k, U, hU, hk⟩

/-- The gcd complexity in `Nε` is at least the least number of remainder calls in a
derivation of the gcd. -/
theorem G_le_callsRemGcd (a b : ℕ) : G a b ≤ callsRemGcd a b := by
  obtain ⟨U, hU, hk⟩ := Nat.sInf_mem (callsRemGcd_set_nonempty' a b)
  unfold callsRemGcd
  rw [← hk]
  exact gcd_certificate_lower hU

/-- The gcd complexity in `(ℕ, rem, eq0)` is at least `G a b`. -/
theorem G_le_callsGcd (a b : ℕ) : G a b ≤ callsGcd a b :=
  (G_le_callsRemGcd a b).trans (callsRemGcd_le_callsGcd a b)

/-- On positive coprime inputs, the complexity of the book's coprimeness relation is exactly
the least number of remainder calls in a derivation of `1`. -/
theorem callsCoprimeness_eq_G {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : Nat.Coprime a b) :
    callsCoprimeness a b = G a b := by
  rw [callsCoprimeness_eq_callsRem ha hb hc, callsRem_eq_D, G_eq_D hc]

/-- **Almost all coprime pairs have coprimeness complexity at least `(1 − ε) log₂ log₂ N`.**
For `0 < ε ≤ 1`, the number of coprime pairs `2 ≤ b < a ≤ N` with
`callsCoprimeness a b ≤ (1 − ε) log₂ log₂ N`, divided by `N²`, tends to `0`. -/
theorem tendsto_card_callsCoprimeness_loglog {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Tendsto (fun N : ℕ => ((((Finset.Icc 2 N) ×ˢ (Finset.Icc 2 N)).filter (fun p : ℕ × ℕ =>
      p.2 < p.1 ∧ Nat.Coprime p.1 p.2 ∧
        (callsCoprimeness p.1 p.2 : ℝ) ≤ (1 - ε) * Real.logb 2 (Real.logb 2 N))).card : ℝ) /
        (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
  classical
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (AlmostAll.tendsto_card_within_loglog hε hε1) (fun N => by positivity) (fun N => ?_)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine Nat.cast_le.mpr (Finset.card_le_card fun p hp => ?_)
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
  obtain ⟨⟨⟨ha2, haN⟩, hb2, hbN⟩, hlt, hc, hle⟩ := hp
  refine Finset.mem_filter.mpr ⟨AlmostAll.mem_box.mpr
    ⟨⟨ha2, haN⟩, ⟨hb2, hbN⟩, hlt⟩, AlmostAll.within_of_D_le hc ?_⟩
  rw [← G_eq_D hc, ← callsCoprimeness_eq_G (by omega) (by omega) hc]
  exact Nat.le_floor hle

end ShortGCD
