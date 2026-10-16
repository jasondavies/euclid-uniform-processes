import ShortGCD.RegisterMachine

namespace ShortGCD.RegisterProgram

lemma Exec.copy {w} (r : Registers w) (d i : Fin w) :
    Exec r 0 (Function.update r d (r i)) := by
  convert Exec.route r (fun j => if j = d then i else j) using 1
  funext j
  by_cases hj : j = d <;> simp [hj]

lemma Exec.pair {w} (r : Registers w) (i j : Fin w) :
    Exec r 0 (inputs w (r i) (r j)) := by
  convert Exec.route r (fun k => if k.val = 1 then j else i) using 1
  funext k
  by_cases hk : k.val = 1 <;> simp [inputs, hk]

/-- The first `t` Euclidean remainders occupy distinct parameter positions.
Unused parameters hold the first input, so no constants are supplied. -/
def stored (w a b t : ℕ) : Registers w :=
  fun i => if i.val < t then remainder a b i.val else a

lemma stored_two {w a b} : stored w a b 2 = inputs w a b := by
  funext i
  simp only [stored, inputs]
  split_ifs with hi h1 h1
  · simp [h1]
  · have : i.val = 0 := by omega
    simp [this]
  · omega
  · rfl

lemma stored_next {w a b t} (ht : t+2 < w)
    (hp : 0 < remainder a b (t+1)) :
    Exec (stored w a b (t+2)) 1 (stored w a b (t+3)) := by
  let i : Fin w := ⟨t, by omega⟩
  let j : Fin w := ⟨t+1, by omega⟩
  let d : Fin w := ⟨t+2, ht⟩
  have hj : stored w a b (t+2) j = remainder a b (t+1) := by simp [stored, j]
  convert Exec.mod (stored w a b (t+2)) i j d (hj ▸ hp) using 1
  funext k
  by_cases hk : k = d
  · subst k
    simp [stored, i, j, d, remainder_rec]
  · have hkd : k.val ≠ t+2 := by simpa [d, Fin.ext_iff] using hk
    simp only [Function.update_of_ne hk, stored]
    by_cases hlt : k.val < t+2
    · simp [hlt, show k.val < t+3 by omega]
    · simp [hlt, show ¬k.val < t+3 by omega]

lemma prefix_exec {w a b t} (hw : t+2 ≤ w)
    (hp : ∀ i, i < t → 0 < remainder a b (i+1)) :
    Exec (inputs w a b) t (stored w a b (t+2)) := by
  induction t with
  | zero => simpa [stored_two] using Exec.refl (inputs w a b)
  | succ t ih =>
    exact (ih (by omega) (fun i hi => hp i (by omega))).trans
      (stored_next (by omega) (hp t (by omega)))

/-- A three-call contraction in fixed registers. Only two temporary parameters
are needed; the final remainder may overwrite one of them. -/
lemma three_registers {w} (r : Registers w) (x y m u v : Fin w)
    (hxv : x ≠ v) (hmv : m ≠ v) (huv : u ≠ v)
    (hm : 0 < r m) (hxy : r x % r m < r y % r m) :
    ∃ z, 0 < z ∧ z ≤ r y % r m - r x % r m ∧ Computes r 3 z := by
  by_cases hz : r x % r m = 0
  · refine ⟨r y % r m, by omega, by omega, ?_⟩
    simpa using Computes.mono ((Exec.mod r y m u hm).finish u) (show 1 ≤ 3 by omega)
  by_cases hs : r x % r m ≤ r y % r m - r x % r m
  · refine ⟨r x % r m, by omega, hs, ?_⟩
    simpa using Computes.mono ((Exec.mod r x m u hm).finish u) (show 1 ≤ 3 by omega)
  let s := Function.update r v (r y % r m)
  let t := Function.update s u (r x % r m)
  have hsx : s x = r x := by simp [s, hxv]
  have hsm : s m = r m := by simp [s, hmv]
  have htpos : 0 < t u := by simp [t]; omega
  have hrem : t v % t u = r y % r m - r x % r m := by
    simp only [t, Function.update_of_ne huv.symm, Function.update_self, s]
    conv_lhs => rw [show r y % r m = (r y % r m - r x % r m) + r x % r m by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have h₁ : Exec r 1 s := .mod r y m v hm
  have h₂ : Exec s 1 t := by simpa [t, hsx, hsm] using Exec.mod s x m u (hsm ▸ hm)
  have h₃ := (Exec.mod t v u u htpos).finish u
  refine ⟨_, by omega, le_rfl, ?_⟩
  simpa [hrem] using (h₁.trans h₂).then_compute h₃

/-- Prefix positions and the three scratch positions are disjoint. -/
def prefixIndex (h : ℕ) (i : Fin (h+1)) : Fin (h+4) := ⟨i.val, by omega⟩
def modulusIndex (h : ℕ) : Fin (h+4) := ⟨h+1, by omega⟩
def tempU (h : ℕ) : Fin (h+4) := ⟨h+2, by omega⟩
def tempV (h : ℕ) : Fin (h+4) := ⟨h+3, by omega⟩
def reservoir (h : ℕ) (r : Registers (h+4)) : Finset ℕ :=
  Finset.univ.image (fun i : Fin (h+1) => r (prefixIndex h i))

lemma reservoir_update {h} (r : Registers (h+4)) (z : ℕ) :
    reservoir h (Function.update r (modulusIndex h) z) = reservoir h r := by
  apply Finset.image_congr
  intro i hi
  have hn : prefixIndex h i ≠ modulusIndex h := by
    intro he
    have hh := congrArg Fin.val he
    simp only [prefixIndex, modulusIndex] at hh
    exact (by omega)
  exact Function.update_of_ne hn _ _

lemma register_contract {h L k} (r : Registers (h+4))
    (hR : Reservoir (reservoir h r) L k) (hk : 1 ≤ k)
    (hm : L < r (modulusIndex h)) :
    ∃ z, 0 < z ∧ z*k < r (modulusIndex h) ∧ Computes r 3 z := by
  let m := r (modulusIndex h)
  have hp : 0 < m := by dsimp [m]; omega
  let R := (reservoir h r).image (fun x => x % m)
  have ht : k+1 ≤ R.card := hR m hm
  obtain ⟨u, hu, v, hv, huv, hgap⟩ := exists_small_gap R (by omega) (by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Nat.mod_lt _ hp)
  obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
  have hxy : r (prefixIndex h i) % m < r (prefixIndex h j) % m := by omega
  obtain ⟨z, hz, hzg, hc⟩ := three_registers r (prefixIndex h i) (prefixIndex h j)
    (modulusIndex h) (tempU h) (tempV h)
    (by simp [prefixIndex, tempV, Fin.ext_iff]; omega)
    (by simp [modulusIndex, tempV, Fin.ext_iff])
    (by simp [tempU, tempV, Fin.ext_iff]) hp hxy
  refine ⟨z, hz, ?_, hc⟩
  have hzk : z*k ≤ z*(R.card-1) := Nat.mul_le_mul_left z (by omega)
  have hzuv : z ≤ v-u := by simpa [m, hxu, hyv] using hzg
  exact hzk.trans_lt ((Nat.mul_le_mul_right _ hzuv).trans_lt hgap)

/-- Repeated contractions preserve the stored prefix in the caller. -/
lemma register_iterate {h L k} (hk : 1 ≤ k) (J : ℕ)
    (r : Registers (h+4)) (hR : Reservoir (reservoir h r) L k)
    (hp : 0 < r (modulusIndex h)) (hs : r (modulusIndex h) ≤ L*k^J) :
    ∃ z, 0 < z ∧ z ≤ L ∧ Exec r (3*J) (Function.update r (modulusIndex h) z) := by
  induction J generalizing r with
  | zero =>
    refine ⟨r (modulusIndex h), hp, by simpa using hs, ?_⟩
    simpa using Exec.copy r (modulusIndex h) (modulusIndex h)
  | succ J ih =>
    by_cases hsmall : r (modulusIndex h) ≤ L
    · exact ⟨_, hp, hsmall, .mono (Exec.copy r _ _) (by omega)⟩
    obtain ⟨z, hz, hzk, hc⟩ := register_contract r hR hk (by omega)
    let s := Function.update r (modulusIndex h) z
    have hsR : Reservoir (reservoir h s) L k := by simpa [s, reservoir_update] using hR
    have hsz : s (modulusIndex h) = z := by simp [s]
    have hzsize : z ≤ L*k^J := by
      rw [pow_succ, ← Nat.mul_assoc] at hs
      exact (Nat.lt_of_mul_lt_mul_right (hzk.trans_le hs)).le
    obtain ⟨v, hv, hvL, he⟩ := ih s hsR (hsz ▸ hz) (hsz ▸ hzsize)
    refine ⟨v, hv, hvL, ?_⟩
    simpa [s, Function.update_idem, Nat.mul_add, Nat.add_comm] using
      (Exec.sub (modulusIndex h) hc).trans he

end ShortGCD.RegisterProgram
