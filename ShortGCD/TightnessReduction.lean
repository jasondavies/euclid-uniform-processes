import ShortGCD.AlmostAll

/-! # The tightness reduction

A derivation of `1` of length `k` from `a, b` is a shape of length `k` whose indices are
below `k + 2` (`exists_shape`). There are at most `(k+2)^(2k)` such shapes, so

    #{(a, b) ∈ box N : Within a b d} ≤ (d+1)(d+2)^(2d) · max_{|S| ≤ d} cnt N S

(`card_within_le_shapes`). If every shape of length at most `κ ln N / ln ln N` reaches `1`
on at most `N^(2−2κ−δ)` pairs, then eventually at most `N^(2−δ/2)` pairs have a
derivation of `1` of length at most `κ ln N / ln ln N` (`eventually_card_within_le`);
on coprime pairs this is `D ≤ κ ln N / ln ln N` (`AlmostAll.within_iff_D_le`): the bound `O(log a / log log a)` is
then tight on almost all coprime pairs.
-/

namespace ShortGCD.TightnessReduction

open Finset ShortGCD.ShapeCount ShortGCD.AlmostAll
open scoped Classical

/-- A derivation from the value list `cur` is the run of a shape. -/
theorem exists_shape : ∀ (l cur avail : List ℕ), (∀ z ∈ avail, z ∈ cur) →
    ValidFrom avail l → ∃ S : Shape, S.length = l.length ∧
      (∀ ij ∈ S, ij.1 < cur.length + l.length ∧ ij.2 < cur.length + l.length) ∧
      runOps S cur = some (cur ++ l)
  | [], cur, _, _, _ => ⟨[], rfl, by simp, by simp [runOps]⟩
  | v :: rest, cur, avail, hsub, ⟨⟨x, hx, y, hy, hy0, hv⟩, hrest⟩ => by
    have hxc := hsub x hx
    have hyc := hsub y hy
    obtain ⟨S', hlen, hidx, hrun⟩ := exists_shape rest (cur ++ [v]) (v :: avail)
      (fun z hz => by
        rcases List.mem_cons.1 hz with rfl | hz
        · simp
        · exact List.mem_append_left _ (hsub z hz)) hrest
    refine ⟨(cur.idxOf x, cur.idxOf y) :: S', by simp [hlen], ?_, ?_⟩
    · intro ij hij
      rcases List.mem_cons.1 hij with rfl | hij
      · have h1 := List.idxOf_lt_length_of_mem hxc
        have h2 := List.idxOf_lt_length_of_mem hyc
        simp only [List.length_cons]
        constructor <;> omega
      · have := hidx ij hij
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        constructor <;> omega
    · have hgx : cur[cur.idxOf x]? = some x := List.getElem?_idxOf hxc
      have hgy : cur[cur.idxOf y]? = some y := List.getElem?_idxOf hyc
      simp only [runOps, hgx, hgy, hy0, ite_false]
      rw [← hv, hrun]
      simp

/-- The shapes of length `k` with indices below `k + 2`. -/
noncomputable def shapes (k : ℕ) : Finset Shape :=
  (Finset.univ : Finset (Fin k → Fin (k + 2) × Fin (k + 2))).image
    (fun f => List.ofFn (fun i => ((f i).1.val, (f i).2.val)))

theorem card_shapes_le (k : ℕ) : (shapes k).card ≤ (k + 2) ^ (2 * k) := by
  refine (Finset.card_image_le).trans ?_
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, pow_mul, sq]

theorem mem_shapes {k : ℕ} {S : Shape} (hlen : S.length = k)
    (hidx : ∀ ij ∈ S, ij.1 < k + 2 ∧ ij.2 < k + 2) : S ∈ shapes k := by
  simp only [shapes, Finset.mem_image, Finset.mem_univ, true_and]
  subst hlen
  refine ⟨fun i => (⟨S[i].1, (hidx _ (List.getElem_mem _)).1⟩,
    ⟨S[i].2, (hidx _ (List.getElem_mem _)).2⟩), ?_⟩
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp

/-- A pair with a derivation of `1` of length at most `d` is reached by a shape of length
at most `d` with small indices. -/
theorem exists_reaching_shape {a b d : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hw : Within a b d) :
    ∃ k ≤ d, ∃ S ∈ shapes k, reaches1 S a b = true := by
  obtain ⟨l, hl, h1, hlen⟩ := hw
  obtain ⟨S, hSlen, hidx, hrun⟩ := exists_shape l [a, b] [a, b] (fun z hz => hz) hl
  refine ⟨l.length, hlen, S, mem_shapes hSlen (fun ij hij => by
    have := hidx ij hij; simpa [Nat.add_comm] using this), ?_⟩
  have h1l : 1 ∈ l := by
    rcases List.mem_cons.1 h1 with h | h
    · omega
    rcases List.mem_cons.1 h with h | h
    · omega
    · exact h
  simp [reaches1, hrun, h1l]

/-- **The tightness reduction.** -/
theorem card_within_le_shapes (N d B : ℕ)
    (hB : ∀ S : Shape, S.length ≤ d → cnt N S ≤ B) :
    ((ShapeCount.box N).filter (fun ab : ℕ × ℕ => Within ab.1 ab.2 d)).card ≤
      (d + 1) * (d + 2) ^ (2 * d) * B := by
  have hsub : (ShapeCount.box N).filter (fun ab : ℕ × ℕ => Within ab.1 ab.2 d) ⊆
      (Finset.range (d + 1)).biUnion (fun k => (shapes k).biUnion (fun S =>
        (ShapeCount.box N).filter (fun ab : ℕ × ℕ => reaches1 S ab.1 ab.2 = true))) := by
    intro ab hab
    rw [Finset.mem_filter] at hab
    obtain ⟨⟨ha2, -⟩, ⟨hb2, -⟩, -⟩ := mem_box.1 hab.1
    obtain ⟨k, hk, S, hS, hreach⟩ := exists_reaching_shape ha2 hb2 hab.2
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    exact ⟨k, by omega, S, hS, hab.1, hreach⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc ∑ k ∈ Finset.range (d + 1), ((shapes k).biUnion (fun S =>
        (ShapeCount.box N).filter (fun ab : ℕ × ℕ => reaches1 S ab.1 ab.2 = true))).card
      ≤ ∑ k ∈ Finset.range (d + 1), (d + 2) ^ (2 * d) * B := by
        refine Finset.sum_le_sum fun k hk => (Finset.card_biUnion_le).trans ?_
        have hkd : k ≤ d := by simp at hk; omega
        calc ∑ S ∈ shapes k, ((ShapeCount.box N).filter
              (fun ab : ℕ × ℕ => reaches1 S ab.1 ab.2 = true)).card
            ≤ ∑ S ∈ shapes k, B := by
              refine Finset.sum_le_sum fun S hS => ?_
              have hlen : S.length = k := by
                simp only [shapes, Finset.mem_image] at hS
                obtain ⟨f, -, rfl⟩ := hS
                simp
              exact hB S (by omega)
          _ = (shapes k).card * B := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (d + 2) ^ (2 * d) * B := by
              gcongr
              refine (card_shapes_le k).trans ?_
              calc (k + 2) ^ (2 * k) ≤ (d + 2) ^ (2 * k) := Nat.pow_le_pow_left (by omega) _
                _ ≤ (d + 2) ^ (2 * d) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = (d + 1) * (d + 2) ^ (2 * d) * B := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

/-- `(d+1)(d+2)^(2d) ≤ log N · N^(2κ)` once `d ≤ κ log N / log log N` and `N` is large. -/
theorem shape_factor_le {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ d : ℕ,
      (d : ℝ) ≤ κ * Real.log N / Real.log (Real.log N) →
      (((d + 1) * (d + 2) ^ (2 * d) : ℕ) : ℝ) ≤ Real.log N * (N : ℝ) ^ (2 * κ) := by
  have hL : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLL : Filter.Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) Filter.atTop
      Filter.atTop := Real.tendsto_log_atTop.comp hL
  filter_upwards [hL.eventually_ge_atTop 4, hLL.eventually_ge_atTop (2 * κ),
    hLL.eventually_ge_atTop 1, Filter.eventually_ge_atTop 2] with N hL4 hLLk hLL1 hN2 d hd
  set L := Real.log (N : ℝ) with hLdef
  set LL := Real.log L with hLLdef
  have hLpos : 0 < L := by linarith
  have hLLpos : 0 < LL := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hdL : (d : ℝ) ≤ L / 2 := by
    calc (d : ℝ) ≤ κ * L / LL := hd
      _ ≤ κ * L / (2 * κ) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hLLk
      _ = L / 2 := by field_simp
  have hd2 : (d : ℝ) + 2 ≤ L := by linarith
  have hd1 : (d : ℝ) + 1 ≤ L := by linarith
  have hpow : ((d : ℝ) + 2) ^ (2 * d) ≤ (N : ℝ) ^ (2 * κ) := by
    calc ((d : ℝ) + 2) ^ (2 * d) ≤ L ^ (2 * d) := by gcongr
      _ = Real.exp (2 * d * LL) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos hLpos, ← hLLdef]
          congr 1; push_cast; ring
      _ ≤ Real.exp (2 * κ * L) := by
          apply Real.exp_le_exp.2
          have : (d : ℝ) * LL ≤ κ * L := by
            rw [le_div_iff₀ hLLpos] at hd; linarith
          linarith
      _ = (N : ℝ) ^ (2 * κ) := by
          rw [Real.rpow_def_of_pos hN0, hLdef]; ring_nf
  push_cast
  calc ((d : ℝ) + 1) * ((d : ℝ) + 2) ^ (2 * d) ≤ L * (N : ℝ) ^ (2 * κ) := by
        gcongr
    _ = Real.log N * (N : ℝ) ^ (2 * κ) := rfl

/-- **Tightness from the per-shape bound.** -/
theorem eventually_card_within_le {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ)
    (hPSB : ∀ᶠ N : ℕ in Filter.atTop, ∀ S : Shape,
      (S.length : ℝ) ≤ κ * Real.log N / Real.log (Real.log N) →
      (cnt N S : ℝ) ≤ (N : ℝ) ^ (2 - 2 * κ - δ)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (((ShapeCount.box N).filter (fun ab : ℕ × ℕ =>
        Within ab.1 ab.2 ⌊κ * Real.log N / Real.log (Real.log N)⌋₊)).card : ℝ) ≤
        (N : ℝ) ^ (2 - δ / 2) := by
  filter_upwards [hPSB, shape_factor_le hκ, eventually_log_le_rpow (K := 1) (by positivity : (0:ℝ) < δ / 2) zero_le_one,
    Filter.eventually_ge_atTop 3,
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)).eventually_ge_atTop 0] with N hN hfac hlog hN3 hLL0
  set x := κ * Real.log N / Real.log (Real.log N) with hx
  set d := ⌊x⌋₊ with hd
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hx0 : 0 ≤ x := by
    rw [hx]; simp only [Function.comp] at hLL0; positivity
  have hdx : (d : ℝ) ≤ x := Nat.floor_le hx0
  -- every shape of length ≤ d satisfies the hypothesis
  set B : ℕ := ⌊(N : ℝ) ^ (2 - 2 * κ - δ)⌋₊
  have hB : ∀ S : Shape, S.length ≤ d → cnt N S ≤ B := by
    intro S hS
    apply Nat.le_floor
    apply hN S
    calc (S.length : ℝ) ≤ d := by exact_mod_cast hS
      _ ≤ x := hdx
  have hR := card_within_le_shapes N d B hB
  have hBR : (B : ℝ) ≤ (N : ℝ) ^ (2 - 2 * κ - δ) := Nat.floor_le (by positivity)
  have hfacd := hfac d hdx
  calc (((ShapeCount.box N).filter (fun ab : ℕ × ℕ => Within ab.1 ab.2 d)).card : ℝ)
      ≤ (((d + 1) * (d + 2) ^ (2 * d) : ℕ) : ℝ) * B := by exact_mod_cast hR
    _ ≤ (Real.log N * (N : ℝ) ^ (2 * κ)) * (N : ℝ) ^ (2 - 2 * κ - δ) := by
        gcongr
    _ = Real.log N * (N : ℝ) ^ (2 - δ) := by
        rw [mul_assoc, ← Real.rpow_add hN0]; ring_nf
    _ ≤ (N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (2 - δ) := by
        gcongr; linarith
    _ = (N : ℝ) ^ (2 - δ / 2) := by
        rw [← Real.rpow_add hN0]; ring_nf

end ShortGCD.TightnessReduction
