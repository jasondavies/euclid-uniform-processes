import ShortGCD.Composition

/-! # Normalization and the worst-case cost `sizeCost`

Derivations commute with scaling and with division by a common divisor, so `G` is homogeneous
and `G a b = G (a/g) (b/g)` for `g = gcd(a, b)`; this reduces the recurrence to coprime inputs.
`sizeCost M`, the worst case of `G` over inputs `≤ M`, is the paper's `T̂(M)`.
-/

namespace ShortGCD

theorem Derives.divide {S T n g} (h : Derives S n T) (hg : 0 < g)
    (hd : ∀ x ∈ S, g ∣ x) :
    Derives (S.image (· / g)) n (T.image (· / g)) := by
  induction h with
  | refl => exact .refl _
  | @step T n x y h hx hy hp ih =>
    have hxg := h.dvd hd x hx
    have hyg := h.dvd hd y hy
    have hyP : 0 < y/g := Nat.div_pos (Nat.le_of_dvd hp hyg) hg
    have he : (x % y)/g = (x/g) % (y/g) := by
      have hex : g*(x/g) = x := Nat.mul_div_cancel' hxg
      have hey : g*(y/g) = y := Nat.mul_div_cancel' hyg
      have hh : g*((x/g)%(y/g)) = x%y := by
        rw [← Nat.mul_mod_mul_left,hex,hey]
      rw [← hh,Nat.mul_div_cancel_left _ hg]
    simpa [Finset.image_insert,he] using Derives.step ih
      (Finset.mem_image_of_mem (· / g) hx) (Finset.mem_image_of_mem (· / g) hy) hyP

theorem Generates.scale {S k w g} (h : Generates S k w) (hg : 0 < g) :
    Generates (S.image (g * ·)) k (g*w) := by
  obtain ⟨n,T,hn,hd,hw⟩ := h
  exact ⟨n,_,hn,hd.scale hg,Finset.mem_image_of_mem _ hw⟩

theorem Generates.divide {S k w g} (h : Generates S k w) (hg : 0 < g)
    (hd : ∀ x ∈ S, g ∣ x) : Generates (S.image (· / g)) k (w/g) := by
  obtain ⟨n,T,hn,hder,hw⟩ := h
  exact ⟨n,_,hn,hder.divide hg hd,Finset.mem_image_of_mem _ hw⟩

/-- Homogeneity of the exact minimum value-generation complexity. -/
theorem G_scale (a b : ℕ) {g : ℕ} (hg : 0 < g) : G (g*a) (g*b) = G a b := by
  apply Nat.le_antisymm
  · apply G_le
    simpa [Nat.gcd_mul_left] using (generates_G a b).scale hg
  · apply G_le
    have hh := (generates_G (g*a) (g*b)).divide hg (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact dvd_mul_right _ _)
    simpa [Nat.gcd_mul_left,Nat.mul_div_cancel_left _ hg] using hh

/-- Normalization by the gcd preserves the exact number of calls. -/
theorem G_normalize {a b : ℕ} (hp : 0 < Nat.gcd a b) :
    G a b = G (a/Nat.gcd a b) (b/Nat.gcd a b) := by
  have hh := G_scale (a/Nat.gcd a b) (b/Nat.gcd a b) hp
  simpa [Nat.mul_div_cancel' (Nat.gcd_dvd_left a b),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)] using hh

/-- `sizeCost M`: the maximum of `G a b` over `a, b ≤ M`, the worst-case number of remainder
calls at size `M` (the paper's `T̂(M)`). -/
noncomputable def sizeCost (M : ℕ) : ℕ :=
  (Finset.range (M+1)).sup (fun a => (Finset.range (M+1)).sup (G a))

theorem G_le_sizeCost {a b M} (ha : a ≤ M) (hb : b ≤ M) : G a b ≤ sizeCost M :=
  Finset.le_sup_of_le (Finset.mem_range.mpr (by omega))
    (Finset.le_sup (Finset.mem_range.mpr (by omega)))

theorem sizeCost_bound (M : ℕ) : GBound M (sizeCost M) := by
  intro a b ha hb
  exact (generates_G a b).mono_cost (G_le_sizeCost ha hb)

theorem sizeCost_le {M K} (h : GBound M K) : sizeCost M ≤ K := by
  apply Finset.sup_le
  intro a ha
  apply Finset.sup_le
  intro b hb
  exact G_le (h a b (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp ha))
    (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hb)))

end ShortGCD
