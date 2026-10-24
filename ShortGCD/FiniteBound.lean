module

public import ShortGCD.Euclid

@[expose] public section

/-! # The finite recurrence for `sizeCost`

`coprime_step` combines the two branches for a coprime pair `b < a ≤ A`: a small coprime pair
early in the Euclidean sequence (cost `h + 1 + T̂(L)`), or a long prefix used as a reservoir
(cost `h + 3J + 2 + 2T̂(M)`). Normalization by the gcd extends this to all inputs, giving the
recurrence `sizeCost_step` that `UpperBound` and `SharpBound` iterate.
-/

namespace ShortGCD

/-- An explicit finite version of the two-branch construction. All parameters are
natural numbers; the size and contraction hypotheses involve no real arithmetic. -/
theorem coprime_step {a b A L M h k J : ℕ}
    (hab : b < a) (hb : 0 < b) (ha : a ≤ A) (hcop : Nat.Coprime a b)
    (hL : 1 ≤ L) (hh : 0 < h) (hk : 1 ≤ k) (hkh : k^2 < h ∨ 3*k ≤ h)
    (hthreshold : 2*A ≤ M*L) (hpower : A ≤ M*k^J) :
    Generates {a,b}
      (max (h+1+sizeCost L) (h+3*J+2+2*sizeCost M)) 1 := by
  rcases euclid_dichotomy hab hb hcop hL hh with hearly | ⟨hlarge,hder⟩
  · obtain ⟨c,s,n,T,hn,hd,hc,hs,hcL,hsL,hcs⟩ := hearly
    have hg := (sizeCost_bound L c s hcL hsL).enlarge
      (show ({c,s}:Finset ℕ) ⊆ T from by
        intro z hz
        simp only [Finset.mem_insert,Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption)
    rw [hcs.gcd_eq_one] at hg
    exact (hd.then_generate hg).mono_cost ((by omega : n+sizeCost L ≤ h+1+sizeCost L).trans (le_max_left _ _))
  · let r := remainder a b
    let q := fun i => r i / r (i+1)
    have hpos : ∀ i, i ≤ h → 0 < r i := by
      intro i hi
      exact lt_trans (by omega) (hlarge i hi)
    have hpos' : ∀ i, i < h → 0 < r (i+1) := fun i hi => hpos (i+1) (by omega)
    have hdesc := remainder_desc hab hpos'
    have hrec : ∀ i, r i = q i*r (i+1)+r (i+2) := by
      intro i
      dsimp [q,r]
      rw [remainder_rec]
      simpa [Nat.mul_comm] using (Nat.div_add_mod (r i) (r (i+1))).symm
    have hqpos : ∀ i, i+1 ≤ h → 0 < q i := fun i hi =>
      Nat.div_pos (hdesc i (by omega)).le (hpos (i+1) (by omega))
    have hthr : 2*a ≤ M*r h :=
      (Nat.mul_le_mul_left 2 ha).trans (hthreshold.trans (Nat.mul_le_mul_left M (hlarge h le_rfl).le))
    have hR : Reservoir ((Finset.range (h+1)).image r) M k := by
      rcases hkh with hkh | hkh
      · exact prefix_reservoir r q a h M k hpos
          (fun i _ => remainder_bound hab.le i) (remainder_lower hab hpos')
          (fun i _ => (remainder_gcd a b i).trans hcop.gcd_eq_one)
          (fun i hi => hqpos i (by omega)) (fun i _ => hrec i) hthr hkh
      · exact prefix_reservoir_three r q a h M k (hpos h le_rfl)
          (fun i _ => remainder_bound hab.le i) (remainder_lower hab hpos')
          (fun i _ => (remainder_gcd a b i).trans hcop.gcd_eq_one)
          hqpos (fun i _ => hrec i) hthr hkh
    have hfinish := large_branch hder
      (a := a) (b := b) (m := r h) (L := M) (k := k) (J := J)
      (by simpa using mem_euclidStore (a := a) (b := b) (n := h) (i := 0) (by omega))
      (by simpa using mem_euclidStore (a := a) (b := b) (n := h) (i := 1) (by omega))
      (mem_euclidStore (by omega)) (hpos h le_rfl)
      (Finset.image_subset_image (Finset.range_mono (by omega))) hR hk
      ((remainder_bound hab.le h).trans (ha.trans hpower)) (sizeCost_bound M) hcop
    exact hfinish.mono_cost (le_max_right _ _)

theorem G_symm (a b : ℕ) : G a b = G b a := by
  apply Nat.le_antisymm <;> apply G_le
  · simpa [Finset.pair_comm,Nat.gcd_comm] using generates_G b a
  · simpa [Finset.pair_comm,Nat.gcd_comm] using generates_G a b

@[simp] theorem G_self (a : ℕ) : G a a = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply G_le
  simpa using (Generates.available (S := {a,a}) (k := 0) (w := a) (by simp))

@[simp] theorem G_zero_right (a : ℕ) : G a 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply G_le
  simpa using (Generates.available (S := {a,0}) (k := 0) (w := a) (by simp))

/-- **The recurrence.** If `L ≥ 1`, `h > 0`, `k ≥ 1`, `k² < h` or `3k ≤ h`, `2A ≤ ML` and
`A ≤ M k^J`, then
`T̂(A) ≤ max(h + 1 + T̂(L), h + 3J + 2 + 2T̂(M))`. Non-coprime and zero inputs are covered
through normalization. -/
theorem sizeCost_step {A L M h k J : ℕ}
    (hL : 1 ≤ L) (hh : 0 < h) (hk : 1 ≤ k) (hkh : k^2 < h ∨ 3*k ≤ h)
    (hthreshold : 2*A ≤ M*L) (hpower : A ≤ M*k^J) :
    sizeCost A ≤ max (h+1+sizeCost L) (h+3*J+2+2*sizeCost M) := by
  have hordered : ∀ a b, b < a → a ≤ A → G a b ≤
      max (h+1+sizeCost L) (h+3*J+2+2*sizeCost M) := by
    intro a b hab ha
    by_cases hb0 : b = 0
    · simp [hb0]
    have hb : 0 < b := by omega
    let g := Nat.gcd a b
    have hg : 0 < g := Nat.gcd_pos_of_pos_right a hb
    have hga : g*(a/g) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
    have hgb : g*(b/g) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
    have hba' : b/g < a/g := by nlinarith
    have hb' : 0 < b/g := Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) hg
    rw [G_normalize hg]
    apply G_le
    have hc := coprime_step hba' hb' ((Nat.div_le_self a g).trans ha)
      (Nat.coprime_div_gcd_div_gcd hg) hL hh hk hkh hthreshold hpower
    simpa [(Nat.coprime_div_gcd_div_gcd hg).gcd_eq_one] using hc
  apply sizeCost_le
  intro a b ha hb
  apply (generates_G a b).mono_cost
  rcases lt_trichotomy b a with hab | hab | hab
  · exact hordered a b hab ha
  · subst b; simp
  · rw [G_symm]; exact hordered b a hab hb

end ShortGCD
