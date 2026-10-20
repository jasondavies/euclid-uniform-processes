import Mathlib

/-! # Straight-line remainder derivations

The basic model of the upper bound: a finite store of naturals grows by remainder calls
`x mod y` with `x, y` in the store and `y > 0`, and the cost is the number of calls. Besides
composition, scaling and divisibility, this module proves the three-call step `three_calls`
behind the contraction and the identity `gcd_recombine` used to finish from a small modulus.
-/

namespace ShortGCD

/-- A straight-line derivation: each step is remainder with an available positive divisor.
The index counts calls, including repeated calls. No constants are introduced. -/
inductive Derives : Finset ℕ → ℕ → Finset ℕ → Prop
  | refl (S) : Derives S 0 S
  | step {S T n x y} : Derives S n T → x ∈ T → y ∈ T → 0 < y →
      Derives S (n + 1) (insert (x % y) T)

/-- `Generates S k w`: some derivation from `S` with at most `k` remainder calls has `w` in its
final store. -/
def Generates (S : Finset ℕ) (k w : ℕ) : Prop :=
  ∃ n T, n ≤ k ∧ Derives S n T ∧ w ∈ T

theorem Derives.subset {S T n} (h : Derives S n T) : S ⊆ T := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ _ _ _ ih => exact ih.trans (Finset.subset_insert _ _)

theorem Derives.mono {S T n} (h : Derives S n T) (U : Finset ℕ) :
    Derives (S ∪ U) n (T ∪ U) := by
  induction h with
  | refl => exact .refl _
  | step h hx hy hp ih =>
      simpa [Finset.insert_union] using Derives.step ih
        (Finset.mem_union_left _ hx) (Finset.mem_union_left _ hy) hp

theorem Derives.trans {S T U n k} (h : Derives S n T) (g : Derives T k U) :
    Derives S (n + k) U := by
  induction g with
  | refl => simpa using h
  | step g hx hy hp ih => simpa [Nat.add_assoc] using Derives.step ih hx hy hp

theorem Generates.available {S k w} (hw : w ∈ S) : Generates S k w :=
  ⟨0, S, Nat.zero_le _, .refl _, hw⟩

theorem Generates.mono_cost {S k l w} (h : Generates S k w) (hkl : k ≤ l) :
    Generates S l w := by
  obtain ⟨n,T,hn,hd,hw⟩ := h
  exact ⟨n,T,hn.trans hkl,hd,hw⟩

theorem Generates.mod {S x y} (hx : x ∈ S) (hy : y ∈ S) (hp : 0 < y) :
    Generates S 1 (x % y) :=
  ⟨1, _, le_rfl, .step (.refl _) hx hy hp, Finset.mem_insert_self _ _⟩

/-- The arithmetic heart of the three-call contraction. `u,v` are selected residues;
subtraction in the statement is analysis, not an instruction of the derivation. -/
theorem three_calls {S : Finset ℕ} {m x y u v : ℕ}
    (hm : 0 < m) (hxm : x ∈ S) (hym : y ∈ S) (hmm : m ∈ S)
    (hu : x % m = u) (hv : y % m = v) (huv : u < v) :
    ∃ w, 0 < w ∧ w ≤ v - u ∧ Generates S 3 w := by
  by_cases hu0 : u = 0
  · refine ⟨v, by omega, by omega, ?_⟩
    exact hv ▸ (Generates.mod hym hmm hm).mono_cost (by omega)
  by_cases hsmall : u ≤ v - u
  · refine ⟨u, by omega, hsmall, ?_⟩
    exact hu ▸ (Generates.mod hxm hmm hm).mono_cost (by omega)
  have huP : 0 < u := by omega
  have hrem : v % u = v - u := by
    conv_lhs => rw [show v = (v - u) + u from by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have h₁ : Derives S 1 (insert v S) := by
    simpa [hv] using Derives.step (.refl S) hym hmm hm
  have h₂ : Derives S 2 (insert u (insert v S)) := by
    simpa [hu] using Derives.step h₁ (Finset.mem_insert_of_mem hxm)
      (Finset.mem_insert_of_mem hmm) hm
  have h₃ := Derives.step h₂ (x := v) (y := u) (by simp) (by simp) huP
  refine ⟨v-u, by omega, le_rfl, 3, insert (v % u) (insert u (insert v S)), le_rfl, ?_, ?_⟩
  · simpa using h₃
  · simp [hrem]

/-- Common divisors are preserved by every instruction. -/
theorem Derives.dvd {S T n d} (h : Derives S n T) (hd : ∀ x ∈ S, d ∣ x) :
    ∀ x ∈ T, d ∣ x := by
  induction h with
  | refl => exact hd
  | step h hx hy hp ih =>
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact (Nat.dvd_mod_iff (ih _ hy)).mpr (ih _ hx)
    · exact ih z hz

/-- Scaling a derivation costs exactly the same number of calls. -/
theorem Derives.scale {S T n} (h : Derives S n T) {g : ℕ} (hg : 0 < g) :
    Derives (S.image (g * ·)) n (T.image (g * ·)) := by
  induction h with
  | refl => exact .refl _
  | step h hx hy hp ih =>
    simpa [Finset.image_insert, Nat.mul_mod_mul_left] using
      Derives.step ih (Finset.mem_image_of_mem (g * ·) hx)
        (Finset.mem_image_of_mem (g * ·) hy) (Nat.mul_pos hg hp)

/-- The two small recursive gcd computations recover the original gcd, without
assuming that the auxiliary modulus is coprime to either input. -/
theorem gcd_recombine (a b m : ℕ) :
    Nat.gcd (Nat.gcd m (a % m)) (b % m) = Nat.gcd m (Nat.gcd a b) := by
  have hma : Nat.gcd m (a % m) = Nat.gcd m a := by
    rw [Nat.gcd_comm m (a % m), ← Nat.gcd_rec]
  rw [hma, ← Nat.gcd_assoc]
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    exact (Nat.dvd_mod_iff ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))).mp
      (Nat.gcd_dvd_right _ _)
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    exact (Nat.dvd_mod_iff ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))).mpr
      (Nat.gcd_dvd_right _ _)

end ShortGCD
