module

public import ShortGCD.TailEuclid
public import ShortGCD.Euclid

@[expose] public section

/-! # A reusable prefix with mutable scratch registers

The prefix remains in fixed slots through every contraction. The modulus and
scratch slots may change; no saved caller is used to restore their old values.
-/
namespace ShortGCD.TailProgram

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

/-- Register layout at width `h + 4`: prefix slots `0, …, h`, the modulus at `h + 1`, and two
scratch residues at `h + 2` and `h + 3`. -/
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

/-- The stored prefix is unchanged; scratch registers need not be restored. -/
def KeepsPrefix {h} (r s : Registers (h+4)) : Prop :=
  ∀ i : Fin (h+1), s (prefixIndex h i) = r (prefixIndex h i)

lemma KeepsPrefix.trans {h} {r s t : Registers (h+4)}
    (h1 : KeepsPrefix r s) (h2 : KeepsPrefix s t) : KeepsPrefix r t :=
  fun i => (h2 i).trans (h1 i)

lemma KeepsPrefix.reservoir {h} {r s : Registers (h+4)} (h : KeepsPrefix r s) :
    reservoir _ s = reservoir _ r := by
  apply Finset.image_congr
  intro i _; exact h i

@[simp] lemma prefix_ne_m {h} (i : Fin (h+1)) : prefixIndex h i ≠ modulusIndex h := by
  intro he; have := congrArg Fin.val he; simp [prefixIndex,modulusIndex] at this; omega
@[simp] lemma prefix_ne_u {h} (i : Fin (h+1)) : prefixIndex h i ≠ tempU h := by
  intro he; have := congrArg Fin.val he; simp [prefixIndex,tempU] at this; omega
@[simp] lemma prefix_ne_v {h} (i : Fin (h+1)) : prefixIndex h i ≠ tempV h := by
  intro he; have := congrArg Fin.val he; simp [prefixIndex,tempV] at this; omega

lemma local_contract {h} (r : Registers (h+4)) (i j : Fin (h+1))
    (hm : 0 < r (modulusIndex h))
    (hxy : r (prefixIndex h i) % r (modulusIndex h) <
      r (prefixIndex h j) % r (modulusIndex h)) :
    ∃ t, Exec r 3 t ∧ KeepsPrefix r t ∧ 0 < t (modulusIndex h) ∧
      t (modulusIndex h) ≤ r (prefixIndex h j) % r (modulusIndex h) -
        r (prefixIndex h i) % r (modulusIndex h) := by
  let m := modulusIndex h
  let u := tempU h
  let v := tempV h
  let x := r (prefixIndex h i) % r m
  let y := r (prefixIndex h j) % r m
  change x < y at hxy
  let s := Function.update r v y
  let t := Function.update s u x
  have hmu : m ≠ u := by simp [m,u,modulusIndex,tempU,Fin.ext_iff]
  have hmv : m ≠ v := by simp [m,v,modulusIndex,tempV,Fin.ext_iff]
  have huv : u ≠ v := by simp [u,v,tempU,tempV,Fin.ext_iff]
  have hsm : s m = r m := by simp [s,hmv]
  have hsx : s (prefixIndex h i) = r (prefixIndex h i) := by simp [s,v]
  have htu : t u = x := by simp [t]
  have htv : t v = y := by simp [t,s,Ne.symm huv]
  have he : Exec r 2 t := by
    have h1 : Exec r 1 s := .mod r (prefixIndex h j) m v hm
    have h2 : Exec s 1 t := by simpa [t,hsx,hsm] using Exec.mod s (prefixIndex h i) m u (hsm ▸ hm)
    exact h1.trans h2
  have hkeep (z : ℕ) : KeepsPrefix r (Function.update t m z) := by
    intro l; simp [t,s,m,u,v]
  by_cases hx : x = 0
  · refine ⟨Function.update t m y,?_,hkeep y,by change 0 < Function.update t m y m; rw [Function.update_self]; omega,?_⟩
    · exact (he.trans (by simpa [htv] using Exec.copy t m v)).mono (by omega)
    · simp [hx,x,y,m]
  by_cases hsmall : x ≤ y-x
  · refine ⟨Function.update t m x,?_,hkeep x,by change 0 < Function.update t m x m; rw [Function.update_self]; omega,?_⟩
    · exact (he.trans (by simpa [htu] using Exec.copy t m u)).mono (by omega)
    · simpa [x,y,m] using hsmall
  · have hmod : y % x = y-x := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    refine ⟨Function.update t m (y%x),?_,hkeep _,?_,?_⟩
    · exact he.trans (by simpa [htu,htv] using Exec.mod t v u m (by simpa [htu] using (show 0 < x by omega)))
    · change 0 < Function.update t m (y%x) m; rw [Function.update_self,hmod]; omega
    · simp [hmod,x,y,m]

lemma register_contract {h L k} (r : Registers (h+4))
    (hR : Reservoir (reservoir h r) L k) (hk : 1 ≤ k)
    (hm : L < r (modulusIndex h)) :
    ∃ t, Exec r 3 t ∧ KeepsPrefix r t ∧ 0 < t (modulusIndex h) ∧
      t (modulusIndex h)*k < r (modulusIndex h) := by
  let m := r (modulusIndex h)
  have hp : 0 < m := by dsimp [m]; omega
  let R := (reservoir h r).image (fun x => x % m)
  have ht : k+1 ≤ R.card := hR m hm
  obtain ⟨u,hu,v,hv,huv,hgap⟩ := exists_small_gap R (by omega)
    (by intro z hz; obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz; exact Nat.mod_lt _ hp)
  obtain ⟨x,hx,hxu⟩ := Finset.mem_image.mp hu
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y,hy,hyv⟩ := Finset.mem_image.mp hv
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨t,he,hkeep,htp,htz⟩ := local_contract r i j hp (by change r (prefixIndex h i) % m < r (prefixIndex h j) % m; omega)
  refine ⟨t,he,hkeep,htp,?_⟩
  have hzuv : t (modulusIndex h) ≤ v-u := by simpa [m,hxu,hyv] using htz
  exact (Nat.mul_le_mul_left _ (show k ≤ R.card-1 by omega)).trans_lt
    ((Nat.mul_le_mul_right _ hzuv).trans_lt hgap)

lemma register_iterate {h L k} (hk : 1 ≤ k) (J : ℕ)
    (r : Registers (h+4)) (hR : Reservoir (reservoir h r) L k)
    (hp : 0 < r (modulusIndex h)) (hs : r (modulusIndex h) ≤ L*k^J) :
    ∃ t, Exec r (3*J) t ∧ KeepsPrefix r t ∧
      0 < t (modulusIndex h) ∧ t (modulusIndex h) ≤ L := by
  induction J generalizing r with
  | zero => exact ⟨r,.refl r,fun _ => rfl,hp,by simpa using hs⟩
  | succ J ih =>
      by_cases hsmall : r (modulusIndex h) ≤ L
      · exact ⟨r,(Exec.refl r).mono (by omega),fun _ => rfl,hp,hsmall⟩
      obtain ⟨s,he,hkeep,hsp,hsk⟩ := register_contract r hR hk (by omega)
      have hsR : Reservoir (reservoir h s) L k := by rw [hkeep.reservoir]; exact hR
      have hsbound : s (modulusIndex h) ≤ L*k^J := by
        rw [pow_succ,← Nat.mul_assoc] at hs
        exact (Nat.lt_of_mul_lt_mul_right (hsk.trans_le hs)).le
      obtain ⟨t,ht,hkt,htp,htL⟩ := ih s hsR hsp hsbound
      exact ⟨t,by simpa [Nat.mul_add,Nat.add_comm] using he.trans ht,hkeep.trans hkt,htp,htL⟩

end ShortGCD.TailProgram
