import ShortGCD.Derivation

/-! # The small-gap lemma

If a store `S` contains a modulus `m > 0` and its elements have `t ≥ 2` distinct residues
modulo `m`, two of the residues are less than `m/(t − 1)` apart, and three remainder calls
produce a positive `w` with `w (t − 1) < m` (`small_remainder`). This is the contraction step
used in `Contraction`.
-/

namespace ShortGCD

/-- Finite packing inequality, in division-free form. -/
theorem exists_small_gap (R : Finset ℕ) {m : ℕ} (ht : 2 ≤ R.card)
    (hR : ∀ r ∈ R, r < m) :
    ∃ u ∈ R, ∃ v ∈ R, u < v ∧ (v-u)*(R.card-1) < m := by
  let f := R.orderEmbOfFin rfl
  by_contra! h
  have hstep : ∀ i (hi : i+1 < R.card),
      m ≤ (f ⟨i+1,hi⟩ - f ⟨i,by omega⟩)*(R.card-1) := by
    intro i hi
    exact h _ (R.orderEmbOfFin_mem rfl _) _ (R.orderEmbOfFin_mem rfl _)
      (f.strictMono (by exact Nat.lt_succ_self i : (⟨i,by omega⟩ : Fin R.card) < ⟨i+1,hi⟩))
  have hpack : ∀ i (hi : i < R.card),
      m*i ≤ (f ⟨i,hi⟩ - f ⟨0,by omega⟩)*(R.card-1) := by
    intro i
    induction i with
    | zero => intro hi; simp
    | succ i ih =>
      intro hi
      have hp := ih (by omega)
      have hs := hstep i hi
      have hf0 : f ⟨0,by omega⟩ ≤ f ⟨i,by omega⟩ := f.monotone (by simp)
      have hfi : f ⟨i,by omega⟩ ≤ f ⟨i+1,hi⟩ := f.monotone (by simp)
      have he : f ⟨i+1,hi⟩ - f ⟨0,by omega⟩ =
          (f ⟨i+1,hi⟩ - f ⟨i,by omega⟩) + (f ⟨i,by omega⟩ - f ⟨0,by omega⟩) := by omega
      rw [he, Nat.add_mul]
      nlinarith
  have hp := hpack (R.card-1) (by omega)
  have hb := hR _ (R.orderEmbOfFin_mem rfl ⟨R.card-1,by omega⟩)
  have hf : f ⟨R.card-1,by omega⟩ - f ⟨0,by omega⟩ < m := by
    change f ⟨R.card-1,by omega⟩ < m at hb
    omega
  exact (Nat.mul_lt_mul_of_pos_right hf (by omega)).not_ge hp

/-- **Small-remainder lemma.** If `m ∈ S`, `m > 0`, and `S` has `t ≥ 2` residues modulo `m`,
three remainder calls from `S` produce some `w > 0` with `w (t − 1) < m`. -/
theorem small_remainder (S : Finset ℕ) {m : ℕ} (hm : 0 < m) (hmem : m ∈ S)
    (ht : 2 ≤ (S.image (fun x => x % m)).card) :
    ∃ w, 0 < w ∧ w*((S.image (fun x => x % m)).card-1) < m ∧ Generates S 3 w := by
  obtain ⟨u,hu,v,hv,huv,hgap⟩ := exists_small_gap (S.image (fun x => x % m)) ht (by
    intro r hr
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
    exact Nat.mod_lt _ hm)
  obtain ⟨x,hx,hxu⟩ := Finset.mem_image.mp hu
  obtain ⟨y,hy,hyv⟩ := Finset.mem_image.mp hv
  obtain ⟨w,hw,hwu,hd⟩ := three_calls hm hx hy hmem hxu hyv huv
  exact ⟨w,hw,(Nat.mul_le_mul_right _ hwu).trans_lt hgap,hd⟩

end ShortGCD
