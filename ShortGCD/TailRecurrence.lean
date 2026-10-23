module

public import ShortGCD.TailPrefix

@[expose] public section

/-! The fixed-prefix recurrence with two ordinary Euclidean finishing loops.
The late branch has no recursive generator subproblem. Scratch values are
updated in place, and only the early branch restarts the same flat generator.
-/
namespace ShortGCD.TailProgram

lemma finish_registers {h M} (hh : 0 < h) (r : Registers (h+4))
    (hp : 0 < r (modulusIndex h)) (hm : r (modulusIndex h) ≤ M)
    (hc : Nat.Coprime (r ⟨0, by omega⟩) (r ⟨1, by omega⟩)) :
    Computes r (2+4*Nat.clog 2 M) 1 := by
  let i : Fin (h+4) := ⟨0, by omega⟩
  let j : Fin (h+4) := ⟨1, by omega⟩
  let m := modulusIndex h
  let u := tempU h
  let v := tempV h
  let a := r i
  let b := r j
  let z := r m
  let s := Function.update r u (a%z)
  let t := Function.update s v (b%z)
  have hju : j ≠ u := by simp [j, u, tempU, Fin.ext_iff]
  have hmu : m ≠ u := by simp [m, u, modulusIndex, tempU, Fin.ext_iff]
  have hmv : m ≠ v := by simp [m, v, modulusIndex, tempV, Fin.ext_iff]
  have huv : u ≠ v := by simp [u, v, tempU, tempV, Fin.ext_iff]
  have hsm : s m = z := by simp [s, hmu, z]
  have hsj : s j = b := by simp [s, hju, b]
  have htm : t m = z := by simp [t, hmv, hsm]
  have htu : t u = a%z := by simp [t, huv, s]
  have htv : t v = b%z := by simp [t]
  have h₁ : Exec r 1 s := .mod r i m u hp
  have h₂ : Exec s 1 t := by simpa [t, hsj, hsm] using Exec.mod s j m v (hsm ▸ hp)
  let d := Nat.gcd z (a%z)
  have hdM : d ≤ M := (Nat.gcd_le_left _ hp).trans hm
  have huM : a%z ≤ M := (Nat.mod_lt _ hp).le.trans hm
  have hvM : b%z ≤ M := (Nat.mod_lt _ hp).le.trans hm
  let n := Nat.clog 2 M
  have hM : M ≤ 2^n := Nat.le_pow_clog (by omega) M
  obtain ⟨q,heuc,hqm,hframe⟩ := euclid_inplace t m u hmu n
    (by rw [htm]; exact hm.trans hM) (by rw [htu]; exact huM.trans hM)
  have hqm' : q m = d := by simpa [htm,htu,d] using hqm
  have hqv : q v = b%z := (hframe v hmv.symm huv.symm).trans htv
  have hlast : Computes q (2*n) (Nat.gcd d (b%z)) :=
    ((computes_maxCost (by omega : 2 ≤ h+4) (hdM.trans hM) (hvM.trans hM)).mono
      (maxCost_pow_le (by omega) n)).pair m v hqm' hqv
  have he : Nat.gcd d (b%z) = 1 := by
    rw [show d = Nat.gcd z (a%z) from rfl, gcd_recombine]
    have hab : Nat.gcd a b = 1 := hc
    rw [hab, Nat.gcd_one_right]
  have hexe : Exec r (1+1+2*n) q := (h₁.trans h₂).trans heuc
  have hf := hexe.then_compute hlast
  rw [he] at hf
  convert hf using 1
  dsimp [n]
  omega

lemma reservoir_stored (h a b : ℕ) :
    reservoir h (stored (h+4) a b (h+1)) =
      (Finset.range (h+1)).image (remainder a b) := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨i.val, Finset.mem_range.mpr i.isLt, ?_⟩
    simp [stored, prefixIndex, i.isLt]
  · intro hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hi' := Finset.mem_range.mp hi
    exact Finset.mem_image.mpr ⟨⟨i, hi'⟩, Finset.mem_univ _, by simp [stored, prefixIndex, hi']⟩

/-- The operational recurrence on coprime inputs, using only a fixed tuple of
`h+4` parameters throughout every recursive invocation. -/
theorem register_coprime_step {a b A L M h k J : ℕ}
    (hab : b < a) (hb : 0 < b) (ha : a ≤ A) (hcop : Nat.Coprime a b)
    (hL : 1 ≤ L) (hh : 0 < h) (hk : 1 ≤ k) (hkh : k^2 < h)
    (hthreshold : 2*A ≤ M*L) (hpower : A ≤ M*k^J) :
    Computes (inputs (h+4) a b)
      (max (h+1+maxCost (h+4) L) (h+3*J+2+4*Nat.clog 2 M)) 1 := by
  by_cases hearly : ∃ i, i < h ∧ remainder a b (i+1) ≤ L
  · classical
    let i := Nat.find hearly
    have hi : i < h ∧ remainder a b (i+1) ≤ L := Nat.find_spec hearly
    have hprev : ∀ j, j < i → L < remainder a b (j+1) := by
      intro j hj
      have hmin := Nat.find_min hearly hj
      omega
    have hp : 0 < remainder a b (i+1) := by
      by_contra! hz
      have heq : remainder a b (i+1) = 0 := by omega
      have hg := remainder_gcd a b i
      rw [heq, Nat.gcd_zero_right, hcop.gcd_eq_one] at hg
      by_cases hi0 : i = 0
      · simp [hi0] at heq
        omega
      · have ht := hprev (i-1) (by omega)
        have hie : i-1+1 = i := by omega
        rw [hie, hg] at ht
        omega
    have hpos : ∀ j, j < i+1 → 0 < remainder a b (j+1) := by
      intro j hj
      by_cases hj' : j < i
      · have ht := hprev j hj'; omega
      · have : j = i := by omega
        simpa [this] using hp
    have hder := prefix_exec (w := h+4) (by omega : i+1+2 ≤ h+4) hpos
    have hsL : remainder a b (i+2) ≤ L := (Nat.mod_lt _ hp).le.trans hi.2
    have hsub := computes_maxCost (by omega : 2 ≤ h+4) hi.2 hsL
    have hpair : Computes (stored (h+4) a b (i+1+2)) (maxCost (h+4) L) 1 := by
      have hc := hsub.pair (r := stored (h+4) a b (i+1+2))
        ⟨i+1, by omega⟩ ⟨i+2, by omega⟩ (by simp [stored]) (by simp [stored])
      simpa [remainder_gcd, hcop.gcd_eq_one] using hc
    exact (hder.then_compute hpair).mono
      ((show i+1+maxCost (h+4) L ≤ h+1+maxCost (h+4) L by omega).trans (le_max_left _ _))
  · have hlarge : ∀ i, i ≤ h → L < remainder a b i := by
      intro i hi
      cases i with
      | zero =>
        have ht : L < remainder a b 1 := by
          by_contra! ht
          exact hearly ⟨0, hh, ht⟩
        simpa using ht.trans hab
      | succ i =>
        by_contra! ht
        exact hearly ⟨i, by omega, ht⟩
    let r := remainder a b
    have hpos : ∀ i, i ≤ h → 0 < r i := fun i hi => lt_trans (by omega) (hlarge i hi)
    have hpos' : ∀ i, i < h → 0 < r (i+1) := fun i hi => hpos (i+1) (by omega)
    have hdesc := remainder_desc hab hpos'
    have hR : Reservoir ((Finset.range (h+1)).image r) M k := by
      apply prefix_reservoir r (fun i => r i / r (i+1)) a h M k hpos
        (fun i _ => remainder_bound hab.le i) (remainder_lower hab hpos')
        (fun i _ => (remainder_gcd a b i).trans hcop.gcd_eq_one)
      · intro i hi
        exact Nat.div_pos (hdesc i (by omega)).le (hpos (i+1) (by omega))
      · intro i hi
        dsimp [r]
        rw [remainder_rec]
        simpa [Nat.mul_comm] using (Nat.div_add_mod (r i) (r (i+1))).symm
      · exact (Nat.mul_le_mul_left 2 ha).trans
          (hthreshold.trans (Nat.mul_le_mul_left M (hlarge h le_rfl).le))
      · exact hkh
    let s := stored (h+4) a b (h+1)
    let m := modulusIndex h
    let t := Function.update s m (r h)
    have hprefix : Exec (inputs (h+4) a b) (h-1) s := by
      have he : h-1+2 = h+1 := by omega
      simpa [s, he] using prefix_exec (w := h+4) (by omega : h-1+2 ≤ h+4)
        (fun i hi => hpos (i+1) (by omega))
    have hcopy : Exec s 0 t := by
      simpa [s, stored, t, r] using Exec.copy s m ⟨h, by omega⟩
    have htR : Reservoir (reservoir h t) M k := by
      simpa [t, m, reservoir_update, s, reservoir_stored] using hR
    have htm : t m = r h := by simp [t]
    obtain ⟨q, he, hkeep, hz, hzM⟩ := register_iterate hk J t htR
      (htm ▸ hpos h le_rfl) (htm ▸ (remainder_bound hab.le h).trans (ha.trans hpower))
    have hqa : q ⟨0, by omega⟩ = a := by
      have hk := hkeep ⟨0,by omega⟩
      simpa [prefixIndex,t,m,modulusIndex,s,stored] using hk
    have hqb : q ⟨1, by omega⟩ = b := by
      have h1m : (⟨1,by omega⟩ : Fin (h+4)) ≠ m := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [m,modulusIndex,Fin.val_mk] at hv
        omega
      have hk := hkeep ⟨1,by omega⟩
      change q ⟨1,by omega⟩ = t ⟨1,by omega⟩ at hk
      rw [hk]
      simp only [t,Function.update_of_ne h1m,s,stored,
        ite_eq_left (show 1 < h+1 by omega),remainder_one]
    have hfinish := finish_registers (M := M) hh q
      (by simpa [m] using hz) (by simpa [m] using hzM)
      (by rw [hqa, hqb]; exact hcop)
    have hres := ((hprefix.trans hcopy).trans he).then_compute hfinish
    exact hres.mono ((show h-1+0+3*J+(2+4*Nat.clog 2 M) ≤
      h+3*J+2+4*Nat.clog 2 M by omega).trans (le_max_right _ _))

/-- **The fixed-width recurrence**, the analogue of `sizeCost_step` for one generator of width
`h + 4`: if `L ≥ 1`, `h > 0`, `k ≥ 1`, `k² < h`, `2A ≤ ML` and `A ≤ M k^J`, then
`maxCost (h+4) A ≤ max(h + 1 + maxCost (h+4) L, h + 3J + 2 + 4 clog₂ M)`. -/
theorem maxCost_step {A L M h k J : ℕ}
    (hL : 1 ≤ L) (hh : 0 < h) (hk : 1 ≤ k) (hkh : k^2 < h)
    (hthreshold : 2*A ≤ M*L) (hpower : A ≤ M*k^J) :
    maxCost (h+4) A ≤ max (h+1+maxCost (h+4) L) (h+3*J+2+4*Nat.clog 2 M) := by
  let K := max (h+1+maxCost (h+4) L) (h+3*J+2+4*Nat.clog 2 M)
  have hordered : ∀ a b, b ≤ a → a ≤ A → Computes (inputs (h+4) a b) K (Nat.gcd a b) := by
    intro a b hab ha
    by_cases heq : b = a
    · subst b; exact computes_self (by omega)
    by_cases hb0 : b = 0
    · subst b; exact computes_zero (by omega)
    have hb : 0 < b := by omega
    let g := Nat.gcd a b
    have hg : 0 < g := Nat.gcd_pos_of_pos_right a hb
    have hga : g*(a/g) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
    have hgb : g*(b/g) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
    have hba' : b/g < a/g := by
      have hlt : b < a := by omega
      nlinarith
    have hb' : 0 < b/g := Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right a b)) hg
    have hcop := Nat.coprime_div_gcd_div_gcd hg
    have hsub := register_coprime_step hba' hb' ((Nat.div_le_self a g).trans ha)
      hcop hL hh hk hkh hthreshold hpower
    have hc : Computes (inputs (h+4) (a/g) (b/g)) K (Nat.gcd (a/g) (b/g)) := by
      rw [show Nat.gcd (a/g) (b/g) = 1 from hcop.gcd_eq_one]
      exact hsub
    simpa [hga, hgb] using computes_scaled_inputs hg hc
  apply maxCost_le (by omega)
  intro a b ha hb
  by_cases hab : b ≤ a
  · exact hordered a b hab ha
  · simpa [Nat.gcd_comm] using computes_swap (by omega : 2 ≤ h+4) (hordered b a (by omega) hb)


theorem maxCost_pow_step {A L m h k J : ℕ}
    (hL : 1 ≤ L) (hh : 0 < h) (hk : 1 ≤ k) (hkh : k^2 < h)
    (hthreshold : 2*A ≤ 2^m*L) (hpower : A ≤ 2^m*k^J) :
    maxCost (h+4) A ≤ max (h+1+maxCost (h+4) L) (h+3*J+2+4*m) := by
  simpa only [Nat.clog_pow 2 m (by omega)] using
    maxCost_step hL hh hk hkh hthreshold hpower

end ShortGCD.TailProgram
