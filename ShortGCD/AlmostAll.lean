import ShortGCD.GcdCertificate
import ShortGCD.ShapeCount

/-! # An almost-all lower bound for remainder derivations

`Within a b d` says that some remainder derivation from `a, b` of length at most `d`
contains `1` (the list semantics `ValidFrom` of `RemainderList`). On coprime pairs this is
`D a b ≤ d` (`within_iff_D_le`).

The argument:
* every generated value is an integer form `u a + w b` (`Rep`);
* if `(a, b)` is `B`-regular, i.e. `|qb − pa| ≥ a/(Bq)` whenever it is nonzero, then a
  positive value with coefficient norm `≤ H` is at least `a/(BH)`, so the quotient of every
  remainder step is at most `BH` and the norm bound grows as `H ↦ H + BH²`;
* producing `1` within `d` steps then forces `a ≤ (2B)^(2^d)/2`; with `B = a^α/2`,
  `α = 2^(-d)`, this is impossible, so every pair with a short derivation is irregular;
* irregular pairs are counted through primitive witnesses `(q, p, r)` and one residue class
  of `a` modulo `q`.
-/

namespace ShortGCD.AlmostAll

open Finset ShortGCD.ShapeCount
open scoped Classical

/-- Some derivation from `a, b` of length at most `d` contains `1`. -/
def Within (a b d : ℕ) : Prop :=
  ∃ l : List ℕ, ValidFrom [a, b] l ∧ 1 ∈ a :: b :: l ∧ l.length ≤ d

theorem within_of_D_le {a b d : ℕ} (h : Nat.Coprime a b) (hd : D a b ≤ d) :
    Within a b d := by
  have hne : {k | ∃ l : List ℕ, ValidFrom [a, b] l ∧ 1 ∈ a :: b :: l ∧ l.length = k}.Nonempty := by
    obtain ⟨k, hk⟩ := derivLen_set_nonempty h
    obtain ⟨F, hF, h1, rfl⟩ := hk
    obtain ⟨l, hl, h1l, -⟩ := (exists_list_iff a b F.card).2 ⟨F, hF, h1, le_rfl⟩
    exact ⟨_, l, hl, h1l, rfl⟩
  obtain ⟨l, hl, h1, hlen⟩ := Nat.sInf_mem hne
  exact ⟨l, hl, h1, by rw [hlen]; exact hd⟩

theorem D_le_of_within {a b d : ℕ} (h : Within a b d) : D a b ≤ d := by
  obtain ⟨l, hl, h1, hlen⟩ := h
  unfold D
  exact (Nat.sInf_le (show l.length ∈ {k | ∃ l : List ℕ, ValidFrom [a, b] l ∧
    1 ∈ a :: b :: l ∧ l.length = k} from ⟨l, hl, h1, rfl⟩)).trans hlen

theorem within_iff_D_le {a b d : ℕ} (h : Nat.Coprime a b) : Within a b d ↔ D a b ≤ d :=
  ⟨D_le_of_within, within_of_D_le h⟩

/-! ## Linear forms and their growth -/

/-- `z = u a + w b` with `|u| + |w| ≤ H`. -/
def Rep (a b : ℕ) (H : ℝ) (z : ℕ) : Prop :=
  ∃ u w : ℤ, (z : ℤ) = u * a + w * b ∧ ((u.natAbs + w.natAbs : ℕ) : ℝ) ≤ H

theorem Rep.mono {a b z : ℕ} {H H' : ℝ} (h : Rep a b H z) (hH : H ≤ H') : Rep a b H' z := by
  obtain ⟨u, w, hz, hn⟩ := h
  exact ⟨u, w, hz, hn.trans hH⟩

/-- `(a, b)` is `B`-regular: `|qb − pa| ≥ a/(Bq)` whenever it is nonzero. -/
def Regular (B : ℝ) (a b : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q → ∀ p : ℤ, (q : ℤ) * b - p * a ≠ 0 →
    (a : ℝ) ≤ B * q * |(((q : ℤ) * b - p * a : ℤ) : ℝ)|

/-- On a regular pair a positive value with a small representation is not small. -/
theorem le_of_rep {B H : ℝ} {a b z : ℕ} (hB : 1 ≤ B) (hreg : Regular B a b)
    (hrep : Rep a b H z) (hz : 0 < z) : (a : ℝ) ≤ B * H * z := by
  obtain ⟨u, w, hzuw, hn⟩ := hrep
  have hu : ((u.natAbs : ℕ) : ℝ) ≤ H := le_trans (by exact_mod_cast Nat.le_add_right _ _) hn
  have hw : ((w.natAbs : ℕ) : ℝ) ≤ H := le_trans (by exact_mod_cast Nat.le_add_left _ _) hn
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  rcases lt_trichotomy w 0 with hw0 | hw0 | hw0
  · -- q = -w, p = u : q b - p a = -z
    have hq : 0 < w.natAbs := Int.natAbs_pos.mpr (by omega)
    have hqz : ((w.natAbs : ℕ) : ℤ) = -w := by omega
    have hr : ((w.natAbs : ℕ) : ℤ) * b - u * a = -(z : ℤ) := by
      rw [hqz]; linear_combination hzuw
    have := hreg w.natAbs hq u (by rw [hr]; omega)
    rw [hr] at this
    have habs : |(((-(z : ℤ)) : ℤ) : ℝ)| = z := by push_cast; rw [abs_neg, abs_of_pos hzR]
    rw [habs] at this
    calc (a : ℝ) ≤ B * (w.natAbs : ℕ) * z := this
      _ ≤ B * H * z := by gcongr
  · -- w = 0 : z = u a ≥ a
    subst hw0
    have hzu : (z : ℤ) = u * a := by simpa using hzuw
    have hu1 : 1 ≤ u := by
      by_contra hcon
      have : u * (a : ℤ) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by positivity)
      omega
    have hza : (a : ℝ) ≤ z := by
      have : (a : ℤ) ≤ z := by rw [hzu]; nlinarith
      exact_mod_cast this
    have hH1 : (1 : ℝ) ≤ H := by
      have : (1 : ℝ) ≤ ((u.natAbs : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ u.natAbs)
      linarith
    have hBH : (1:ℝ) ≤ B * H := one_le_mul_of_one_le_of_one_le hB hH1
    calc (a : ℝ) ≤ z := hza
      _ ≤ B * H * z := le_mul_of_one_le_left hzR.le hBH
  · -- q = w, p = -u : q b - p a = z
    have hq : 0 < w.natAbs := Int.natAbs_pos.mpr (by omega)
    have hqz : ((w.natAbs : ℕ) : ℤ) = w := by omega
    have hr : ((w.natAbs : ℕ) : ℤ) * b - (-u) * a = (z : ℤ) := by
      rw [hqz]; linear_combination -hzuw
    have := hreg w.natAbs hq (-u) (by rw [hr]; omega)
    rw [hr] at this
    have habs : |(((z : ℤ)) : ℝ)| = z := by push_cast; rw [abs_of_pos hzR]
    rw [habs] at this
    calc (a : ℝ) ≤ B * (w.natAbs : ℕ) * z := this
      _ ≤ B * H * z := by gcongr

/-- One remainder step: a value with representations of norm `≤ H` for its operands has one
of norm `≤ H + BH²`. -/
theorem rep_mod {B H : ℝ} {a b x y : ℕ} (hB : 1 ≤ B) (hreg : Regular B a b)
    (hx : Rep a b H x) (hy : Rep a b H y) (hxa : x ≤ a) (hy0 : y ≠ 0) :
    Rep a b (H + B * H * H) (x % y) := by
  obtain ⟨u₁, w₁, hx', hn₁⟩ := hx
  have hyR := le_of_rep hB hreg hy (Nat.pos_of_ne_zero hy0)
  obtain ⟨u₂, w₂, hy', hn₂⟩ := hy
  set q := x / y
  have hmod : x % y = x - y * q := by rw [Nat.mod_eq_sub_mul_div]
  have hqy : y * q ≤ x := Nat.mul_div_le x y
  refine ⟨u₁ - q * u₂, w₁ - q * w₂, ?_, ?_⟩
  · rw [hmod, Nat.cast_sub hqy]; push_cast; rw [hx', hy']; ring
  · -- q ≤ B H
    have hyp : (0 : ℝ) < y := by exact_mod_cast Nat.pos_of_ne_zero hy0
    have hqB : (q : ℝ) ≤ B * H := by
      have h1 : ((y * q : ℕ) : ℝ) ≤ a := by exact_mod_cast hqy.trans hxa
      push_cast at h1
      have : (y : ℝ) * q ≤ B * H * y := h1.trans hyR
      nlinarith
    have hH0 : (0 : ℝ) ≤ H := le_trans (by positivity) hn₁
    have hn : (((u₁ - q * u₂).natAbs + (w₁ - q * w₂).natAbs : ℕ) : ℝ) ≤
        ((u₁.natAbs + w₁.natAbs : ℕ) : ℝ) + q * ((u₂.natAbs + w₂.natAbs : ℕ) : ℝ) := by
      have h1 : (u₁ - q * u₂).natAbs ≤ u₁.natAbs + q * u₂.natAbs := by
        have := Int.natAbs_sub_le u₁ (q * u₂)
        rwa [Int.natAbs_mul, Int.natAbs_natCast] at this
      have h2 : (w₁ - q * w₂).natAbs ≤ w₁.natAbs + q * w₂.natAbs := by
        have := Int.natAbs_sub_le w₁ (q * w₂)
        rwa [Int.natAbs_mul, Int.natAbs_natCast] at this
      have : (u₁ - q * u₂).natAbs + (w₁ - q * w₂).natAbs ≤
          (u₁.natAbs + w₁.natAbs) + q * (u₂.natAbs + w₂.natAbs) := by nlinarith
      exact_mod_cast this
    have hq0 : (0 : ℝ) ≤ q := by positivity
    calc _ ≤ ((u₁.natAbs + w₁.natAbs : ℕ) : ℝ) + q * ((u₂.natAbs + w₂.natAbs : ℕ) : ℝ) := hn
      _ ≤ H + (B * H) * H := by gcongr
      _ = H + B * H * H := by ring

/-- The norm bound after `k` steps. -/
def grow (B : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => grow B k + B * grow B k * grow B k

theorem one_le_grow {B : ℝ} (hB : 0 ≤ B) : ∀ k, 1 ≤ grow B k
  | 0 => le_rfl
  | k + 1 => by
    have := one_le_grow hB k
    simp only [grow]; nlinarith [mul_nonneg (mul_nonneg hB (by linarith : (0:ℝ) ≤ grow B k))
      (by linarith : (0:ℝ) ≤ grow B k)]

theorem grow_mono {B : ℝ} (hB : 0 ≤ B) {k l : ℕ} (hkl : k ≤ l) : grow B k ≤ grow B l := by
  induction hkl with
  | refl => exact le_rfl
  | step _ ih =>
    refine ih.trans ?_
    simp only [grow]
    have := one_le_grow hB ‹_›
    nlinarith [mul_nonneg (mul_nonneg hB (by linarith : (0:ℝ) ≤ grow B _))
      (by linarith : (0:ℝ) ≤ grow B _)]

theorem grow_le {B : ℝ} (hB : 1 ≤ B) : ∀ k, grow B k ≤ (2 * B) ^ (2 ^ k - 1)
  | 0 => by simp [grow]
  | k + 1 => by
    have ih := grow_le hB k
    have h1 := one_le_grow (by linarith : (0:ℝ) ≤ B) k
    simp only [grow]
    have hpow : (2 * B) ^ (2 ^ (k + 1) - 1) = 2 * B * ((2 * B) ^ (2 ^ k - 1)) ^ 2 := by
      have h2 : 2 ^ (k + 1) - 1 = 1 + 2 * (2 ^ k - 1) := by
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        rw [pow_succ]; omega
      rw [h2, pow_add, pow_one, mul_comm 2 (2 ^ k - 1), pow_mul]
    rw [hpow]
    have hg0 : (0 : ℝ) ≤ grow B k := by linarith
    have hBg : 1 ≤ B * grow B k := one_le_mul_of_one_le_of_one_le hB h1
    have hgg : grow B k ≤ B * grow B k * grow B k := by nlinarith
    calc grow B k + B * grow B k * grow B k ≤ 2 * B * grow B k * grow B k := by linarith
      _ ≤ 2 * B * ((2 * B) ^ (2 ^ k - 1)) ^ 2 := by
        rw [mul_assoc, sq]; gcongr

/-- Along a derivation every value is at most `a` and has a representation whose norm
bound grows by `grow`. -/
theorem rep_validFrom {B : ℝ} {a b : ℕ} (hB : 1 ≤ B) (hreg : Regular B a b) :
    ∀ (l avail : List ℕ) (k : ℕ), (∀ z ∈ avail, z ≤ a ∧ Rep a b (grow B k) z) →
      ValidFrom avail l → ∀ z ∈ l, z ≤ a ∧ Rep a b (grow B (k + l.length)) z
  | [], _, _, _, _ => by simp
  | v :: rest, avail, k, havail, ⟨⟨x, hx, y, hy, hy0, hv⟩, hrest⟩ => by
    have hB0 : (0 : ℝ) ≤ B := by linarith
    have hvk : v ≤ a ∧ Rep a b (grow B (k + 1)) v := by
      obtain ⟨hxa, hxr⟩ := havail x hx
      obtain ⟨-, hyr⟩ := havail y hy
      refine ⟨hv ▸ (Nat.mod_le x y).trans hxa, ?_⟩
      rw [hv]
      simpa [grow] using rep_mod hB hreg hxr hyr hxa hy0
    have havail' : ∀ z ∈ v :: avail, z ≤ a ∧ Rep a b (grow B (k + 1)) z := by
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hvk
      · obtain ⟨h1, h2⟩ := havail z hz
        exact ⟨h1, h2.mono (grow_mono hB0 (Nat.le_succ k))⟩
    have ih := rep_validFrom hB hreg rest (v :: avail) (k + 1) havail' hrest
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · obtain ⟨h1, h2⟩ := hvk
      exact ⟨h1, h2.mono (grow_mono hB0 (by simp))⟩
    · obtain ⟨h1, h2⟩ := ih z hz
      exact ⟨h1, h2.mono (le_of_eq (by simp [List.length_cons]; ring_nf))⟩

/-- **Regular pairs need long derivations.** -/
theorem le_of_within_regular {B : ℝ} {a b d : ℕ} (hB : 1 ≤ B) (hreg : Regular B a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hba : b ≤ a) (hw : Within a b d) :
    (a : ℝ) ≤ (2 * B) ^ (2 ^ d) / 2 := by
  obtain ⟨l, hl, h1, hlen⟩ := hw
  have h1l : 1 ∈ l := by
    rcases List.mem_cons.1 h1 with h | h
    · omega
    rcases List.mem_cons.1 h with h | h
    · omega
    · exact h
  have hinit : ∀ z ∈ [a, b], z ≤ a ∧ Rep a b (grow B 0) z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact ⟨le_rfl, 1, 0, by simp, by simp [grow]⟩
    · exact ⟨hba, 0, 1, by simp, by simp [grow]⟩
  obtain ⟨-, hrep⟩ := rep_validFrom hB hreg l [a, b] 0 hinit hl 1 h1l
  have hle := le_of_rep hB hreg hrep one_pos
  simp only [zero_add, Nat.cast_one, mul_one] at hle
  have hg := grow_le hB l.length
  have h2B : (1 : ℝ) ≤ 2 * B := by linarith
  have hmono : (2 * B) ^ (2 ^ l.length - 1) ≤ (2 * B) ^ (2 ^ d - 1) :=
    pow_le_pow_right₀ h2B (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) hlen) 1)
  have hpow : (2 * B) ^ (2 ^ d) = 2 * B * (2 * B) ^ (2 ^ d - 1) := by
    rw [← pow_succ']; congr 1; have : 1 ≤ 2 ^ d := Nat.one_le_two_pow; omega
  rw [hpow]
  calc (a : ℝ) ≤ B * grow B l.length := hle
    _ ≤ B * (2 * B) ^ (2 ^ d - 1) := by gcongr; exact hg.trans hmono
    _ = 2 * B * (2 * B) ^ (2 ^ d - 1) / 2 := by ring

/-! ## Counting irregular pairs -/

theorem mem_box {N : ℕ} {ab : ℕ × ℕ} :
    ab ∈ ShapeCount.box N ↔ (2 ≤ ab.1 ∧ ab.1 ≤ N) ∧ (2 ≤ ab.2 ∧ ab.2 ≤ N) ∧ ab.2 < ab.1 := by
  simp only [ShapeCount.box, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

/-- A primitive witness of irregularity at scale `X`. -/
def Irr (X : ℝ) (a b : ℕ) : Prop :=
  ∃ q p : ℤ, 0 < q ∧ Int.gcd p q = 1 ∧ q * b - p * a ≠ 0 ∧ |q * b - p * a| < a ∧
    (q : ℝ) * |((q * b - p * a : ℤ) : ℝ)| < X

theorem irr_of_not_regular {B X : ℝ} {a b : ℕ} (hB : 1 ≤ B) (hX : (a : ℝ) / B ≤ X)
    (hreg : ¬ Regular B a b) : Irr X a b := by
  unfold Regular at hreg
  push Not at hreg
  obtain ⟨q, hq, p, hr0, hlt⟩ := hreg
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hg : 0 < Int.gcd p q := Int.gcd_pos_of_ne_zero_right p hqZ
  obtain ⟨g, p', q', hg0, hcop, hp, hqq⟩ := Int.exists_gcd_one' hg
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg0
  have hq'pos : 0 < q' := by
    have : (0 : ℤ) < q' * g := by rw [← hqq]; exact_mod_cast hq
    exact pos_of_mul_pos_left this hgZ.le
  set r : ℤ := (q : ℤ) * b - p * a with hr
  set r' : ℤ := q' * b - p' * a with hr'
  have hrr : r = r' * g := by rw [hr, hr', hp, hqq]; ring
  have hr'0 : r' ≠ 0 := by rintro h; rw [h, zero_mul] at hrr; exact hr0 hrr
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg0
  have habs : |(r' : ℝ)| ≤ |(r : ℝ)| := by
    rw [hrr]; push_cast; rw [abs_mul, abs_of_pos (by exact_mod_cast hgZ : (0:ℝ) < g)]
    nlinarith [abs_nonneg (r' : ℝ)]
  have hqle : (q' : ℝ) ≤ q := by
    have : (q : ℤ) = q' * g := hqq
    have h2 : (q' : ℝ) * 1 ≤ q' * g := by
      apply mul_le_mul_of_nonneg_left hgR; exact_mod_cast hq'pos.le
    have h3 : ((q : ℤ) : ℝ) = (q' : ℝ) * g := by exact_mod_cast this
    simp only [Int.cast_natCast] at h3
    linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hBq : 1 ≤ B * q := one_le_mul_of_one_le_of_one_le hB hqR
  have hr_lt : |(r : ℝ)| < a := by
    have := abs_nonneg (r : ℝ)
    nlinarith
  refine ⟨q', p', hq'pos, ?_, hr'0, ?_, ?_⟩
  · rw [Int.gcd_comm] at hcop ⊢; exact (by simpa [Int.gcd_comm] using hcop)
  · have : |(r' : ℝ)| < a := habs.trans_lt hr_lt
    exact_mod_cast this
  · have hBpos : 0 < B := by linarith
    have h1 : (q : ℝ) * |(r : ℝ)| < a / B := by
      rw [lt_div_iff₀ hBpos]; linarith
    have hq'0 : (0 : ℝ) ≤ q' := by exact_mod_cast hq'pos.le
    calc (q' : ℝ) * |(r' : ℝ)| ≤ q * |(r : ℝ)| :=
          mul_le_mul hqle habs (abs_nonneg _) (by linarith)
      _ < a / B := h1
      _ ≤ X := hX

/-- Pairs with a fixed primitive witness `(q, p, r)` share one residue class of `a`. -/
theorem card_fiber_le (N q : ℕ) (hq : 0 < q) (p r : ℤ) (hcop : Int.gcd p q = 1) :
    ((ShapeCount.box N).filter (fun ab : ℕ × ℕ => (q : ℤ) * ab.2 - p * ab.1 = r)).card ≤ N / q + 1 := by
  rw [← Finset.card_range (N / q + 1)]
  apply Finset.card_le_card_of_injOn (fun ab : ℕ × ℕ => ab.1 / q)
  · intro ab hab
    rw [Finset.mem_coe, Finset.mem_filter, mem_box] at hab
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hab.1.1.2)
  · intro ab hab ab' hab' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hab hab'
    simp only at heq
    have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have hdiv : (q : ℤ) ∣ p * ((ab.1 : ℤ) - ab'.1) :=
      ⟨(ab.2 : ℤ) - ab'.2, by linear_combination hab'.2 - hab.2⟩
    have hcop' : Int.gcd (q : ℤ) p = 1 := by rw [Int.gcd_comm]; exact hcop
    have hq1 : (q : ℤ) ∣ (ab.1 : ℤ) - ab'.1 := Int.dvd_of_dvd_mul_right_of_gcd_one hdiv hcop'
    have hmod : ab'.1 ≡ ab.1 [MOD q] := (Nat.modEq_iff_dvd).2 hq1
    have ha : ab.1 = ab'.1 := by
      have h1 := Nat.div_add_mod ab.1 q
      have h2 := Nat.div_add_mod ab'.1 q
      unfold Nat.ModEq at hmod
      rw [heq] at h1
      omega
    have hb : ab.2 = ab'.2 := by
      have h := hab.2
      have h' := hab'.2
      rw [ha] at h
      have : (q : ℤ) * ab.2 = q * ab'.2 := by linarith
      exact_mod_cast mul_left_cancel₀ hqZ this
    exact Prod.ext ha hb

/-- The harmonic sum. -/
theorem sum_inv_le_log (Q : ℕ) (X : ℝ) (hQX : (Q : ℝ) ≤ X) (hX : 1 ≤ X) :
    ∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / q ≤ 1 + Real.log X := by
  have h := harmonic_le_one_add_log Q
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simp only [one_div]
  refine h.trans ?_
  by_cases hQ : Q = 0
  · simp [hQ, Real.log_nonneg hX]
  · have : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero hQ
    have := Real.log_le_log this hQX
    linarith

theorem card_irr_le (N : ℕ) (X : ℝ) (hX1 : 1 ≤ X) (hXN : X ≤ 2 * N) :
    (((ShapeCount.box N).filter (fun ab : ℕ × ℕ => Irr X ab.1 ab.2)).card : ℝ) ≤
      18 * X * N * (1 + Real.log X) := by
  set Q := ⌊X⌋₊ with hQ
  let M : ℕ → ℕ := fun q => ⌊X / q⌋₊
  let T : ℕ → ℤ → ℤ → Finset (ℕ × ℕ) := fun q p r =>
    (ShapeCount.box N).filter (fun ab : ℕ × ℕ => (q : ℤ) * ab.2 - p * ab.1 = r)
  let Ps : ℕ → Finset ℤ := fun q => (Finset.Icc (0 : ℤ) q).filter (fun p => Int.gcd p q = 1)
  let Rs : ℕ → Finset ℤ := fun q => Finset.Icc (-(M q : ℤ)) (M q)
  have hsub : (ShapeCount.box N).filter (fun ab : ℕ × ℕ => Irr X ab.1 ab.2) ⊆
      (Finset.Icc 1 Q).biUnion (fun q => (Ps q).biUnion (fun p => (Rs q).biUnion
        (fun r => T q p r))) := by
    intro ab hab
    simp only [Finset.mem_filter] at hab
    obtain ⟨hbox, q, p, hq, hcop, hr0, hrlt, hX⟩ := hab
    obtain ⟨⟨ha2, haN⟩, ⟨hb2, hbN⟩, hba⟩ := mem_box.1 hbox
    set r : ℤ := q * ab.2 - p * ab.1 with hr
    have hr1 : (1 : ℝ) ≤ |(r : ℝ)| := by
      have : (1 : ℤ) ≤ |r| := Int.one_le_abs hr0
      exact_mod_cast this
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hqX : (q : ℝ) < X := by nlinarith
    have hqn : q = (q.toNat : ℤ) := (Int.toNat_of_nonneg hq.le).symm
    have hqc : ((q.toNat : ℕ) : ℝ) = (q : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) hqn
      simp only [Int.cast_natCast] at h
      exact h.symm
    simp only [Finset.mem_biUnion]
    refine ⟨q.toNat, ?_, p, ?_, r, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      constructor
      · omega
      · apply Nat.le_floor
        rw [hqc]; exact hqX.le
    · simp only [Ps, Finset.mem_filter, Finset.mem_Icc]
      rw [← hqn]
      refine ⟨⟨?_, ?_⟩, hcop⟩
      · by_contra hp
        push Not at hp
        have : r ≥ ab.1 := by
          have h1 : p * (ab.1 : ℤ) ≤ -(ab.1 : ℤ) := by nlinarith
          have h2 : (0 : ℤ) ≤ q * ab.2 := by positivity
          rw [hr]; linarith
        have : |r| ≥ ab.1 := le_trans this (le_abs_self r)
        linarith
      · by_contra hp
        push Not at hp
        have hba' : (ab.2 : ℤ) < ab.1 := by exact_mod_cast hba
        have : r < -(ab.1 : ℤ) := by
          have h1 : (q + 1) * (ab.1 : ℤ) ≤ p * ab.1 := by
            apply mul_le_mul_of_nonneg_right (by omega) (by positivity)
          have h2 : q * (ab.2 : ℤ) < q * ab.1 := by nlinarith
          rw [hr]; nlinarith
        have : |r| > ab.1 := by
          rw [abs_of_neg (by linarith)]; linarith
        linarith
    · simp only [Rs, M, Finset.mem_Icc]
      have hle : (r.natAbs : ℝ) ≤ X / ((q.toNat : ℕ) : ℝ) := by
        rw [hqc, le_div_iff₀ hqR]
        have : (r.natAbs : ℝ) = |(r : ℝ)| := by
          rw [Nat.cast_natAbs]; push_cast; rfl
        rw [this]; linarith
      have hfl : r.natAbs ≤ ⌊X / ((q.toNat : ℕ) : ℝ)⌋₊ := Nat.le_floor hle
      have h1 : |r| ≤ (⌊X / ((q.toNat : ℕ) : ℝ)⌋₊ : ℤ) := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast hfl
      constructor <;> [linarith [neg_abs_le r]; linarith [le_abs_self r]]
    · simp only [T, Finset.mem_filter]
      exact ⟨hbox, by rw [← hqn]⟩
  have hcard := Finset.card_le_card hsub
  have hsum : ((Finset.Icc 1 Q).biUnion (fun q => (Ps q).biUnion (fun p => (Rs q).biUnion
        (fun r => T q p r)))).card ≤
      ∑ q ∈ Finset.Icc 1 Q, (q + 1) * ((2 * M q + 1) * (N / q + 1)) := by
    refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun q hq => ?_)
    have hq1 : 0 < q := by simp at hq; omega
    refine (Finset.card_biUnion_le).trans ?_
    have hPs : (Ps q).card ≤ q + 1 := by
      refine (Finset.card_filter_le _ _).trans ?_
      simp
    calc ∑ p ∈ Ps q, ((Rs q).biUnion fun r => T q p r).card
        ≤ ∑ p ∈ Ps q, (2 * M q + 1) * (N / q + 1) := by
          refine Finset.sum_le_sum fun p hp => ?_
          refine (Finset.card_biUnion_le).trans ?_
          have hcop : Int.gcd p q = 1 := (Finset.mem_filter.1 hp).2
          calc ∑ r ∈ Rs q, (T q p r).card ≤ ∑ r ∈ Rs q, (N / q + 1) :=
                Finset.sum_le_sum fun r _ => card_fiber_le N q hq1 p r hcop
            _ = (Rs q).card * (N / q + 1) := by rw [Finset.sum_const, smul_eq_mul]
            _ ≤ (2 * M q + 1) * (N / q + 1) := by
                gcongr
                simp only [Rs, Int.card_Icc]
                omega
      _ = (Ps q).card * ((2 * M q + 1) * (N / q + 1)) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (q + 1) * ((2 * M q + 1) * (N / q + 1)) := by gcongr
  have hNpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ 2 * N := hX1.trans hXN
    linarith
  have hterm : ∀ q ∈ Finset.Icc 1 Q,
      (((q + 1) * ((2 * M q + 1) * (N / q + 1)) : ℕ) : ℝ) ≤ 18 * X * N * (1 / q) := by
    intro q hq
    simp only [Finset.mem_Icc] at hq
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq.1
    have hqpos : (0 : ℝ) < q := by linarith
    have hqX : (q : ℝ) ≤ X := (Nat.cast_le.2 hq.2).trans (Nat.floor_le (by linarith))
    have hM : (M q : ℝ) ≤ X / q := Nat.floor_le (by positivity)
    have hXq : 1 ≤ X / q := by rw [le_div_iff₀ hqpos]; linarith
    have hNq : ((N / q : ℕ) : ℝ) ≤ N / q := Nat.cast_div_le
    have hNq1 : 1 ≤ 2 * (N : ℝ) / q := by rw [le_div_iff₀ hqpos]; linarith
    push_cast
    have e1 : (q : ℝ) + 1 ≤ 2 * q := by linarith
    have e2 : 2 * (M q : ℝ) + 1 ≤ 3 * (X / q) := by linarith
    have e3 : ((N / q : ℕ) : ℝ) + 1 ≤ 3 * (N / q) := by
      have : (1 : ℝ) ≤ 2 * (N / q) := by rw [mul_div_assoc'] ; exact hNq1
      linarith
    calc ((q : ℝ) + 1) * ((2 * (M q : ℝ) + 1) * (((N / q : ℕ) : ℝ) + 1))
        ≤ (2 * q) * ((3 * (X / q)) * (3 * (N / q))) := by gcongr
      _ = 18 * X * N * (1 / q) := by field_simp; ring
  calc (((ShapeCount.box N).filter (fun ab : ℕ × ℕ => Irr X ab.1 ab.2)).card : ℝ)
      ≤ ((∑ q ∈ Finset.Icc 1 Q, (q + 1) * ((2 * M q + 1) * (N / q + 1)) : ℕ) : ℝ) := by
        exact_mod_cast hcard.trans hsum
    _ = ∑ q ∈ Finset.Icc 1 Q, (((q + 1) * ((2 * M q + 1) * (N / q + 1)) : ℕ) : ℝ) := by
        push_cast; rfl
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, 18 * X * N * (1 / (q : ℝ)) := Finset.sum_le_sum hterm
    _ = 18 * X * N * ∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / q := by rw [Finset.mul_sum]
    _ ≤ 18 * X * N * (1 + Real.log X) := by
        gcongr
        exact sum_inv_le_log Q X (Nat.floor_le (by linarith)) hX1

/-! ## The almost-all bound -/

/-- **Almost-all bound.** At most `40 (2 + ln N) N^(2 − 2^(−d))` pairs `2 ≤ b < a ≤ N` have a
remainder derivation of `1` with at most `d` steps. -/
theorem card_within_le (N d : ℕ) (hN : 1 ≤ N) :
    (((ShapeCount.box N).filter (fun ab : ℕ × ℕ => Within ab.1 ab.2 d)).card : ℝ) ≤
      40 * (2 + Real.log N) * (N : ℝ) ^ (2 - (1 / 2 : ℝ) ^ d) := by
  set α : ℝ := (1 / 2 : ℝ) ^ d with hα
  have hα0 : 0 < α := by positivity
  have hα1 : α ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set X : ℝ := 2 * (N : ℝ) ^ (1 - α) with hX
  have hNpow1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - α) := Real.one_le_rpow hNR (by linarith)
  have hX1 : 1 ≤ X := by linarith
  have hNle : (N : ℝ) ^ (1 - α) ≤ N := by
    have : (N : ℝ) ^ (1 - α) ≤ (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
    rwa [Real.rpow_one] at this
  have hXN : X ≤ 2 * N := by linarith
  set Small := (ShapeCount.box N).filter (fun ab : ℕ × ℕ => (ab.1 : ℝ) ^ α < 2)
  have hsplit : (ShapeCount.box N).filter (fun ab : ℕ × ℕ => Within ab.1 ab.2 d) ⊆
      Small ∪ (ShapeCount.box N).filter (fun ab : ℕ × ℕ => Irr X ab.1 ab.2) := by
    intro ab hab
    rw [Finset.mem_filter] at hab
    obtain ⟨hbox, hw⟩ := hab
    obtain ⟨⟨ha2, haN⟩, ⟨hb2, hbN⟩, hba⟩ := mem_box.1 hbox
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hs : (ab.1 : ℝ) ^ α < 2
    · exact Or.inl ⟨hbox, hs⟩
    · right
      refine ⟨hbox, ?_⟩
      push Not at hs
      have haR : (0 : ℝ) < ab.1 := by exact_mod_cast (by omega : 0 < ab.1)
      set B : ℝ := (ab.1 : ℝ) ^ α / 2 with hBdef
      have hB : 1 ≤ B := by rw [hBdef]; linarith
      apply irr_of_not_regular hB
      · have hdiv : (ab.1 : ℝ) / B = 2 * (ab.1 : ℝ) ^ (1 - α) := by
          rw [hBdef, Real.rpow_sub haR, Real.rpow_one]
          have : (0 : ℝ) < (ab.1 : ℝ) ^ α := Real.rpow_pos_of_pos haR α
          field_simp
        rw [hdiv, hX]
        have : (ab.1 : ℝ) ^ (1 - α) ≤ (N : ℝ) ^ (1 - α) :=
          Real.rpow_le_rpow haR.le (by exact_mod_cast haN) (by linarith)
        linarith
      · intro hreg
        have hle := le_of_within_regular hB hreg ha2 hb2 hba.le hw
        have h2B : (2 * B) ^ (2 ^ d) = (ab.1 : ℝ) := by
          rw [hBdef, show 2 * ((ab.1 : ℝ) ^ α / 2) = (ab.1 : ℝ) ^ α by ring,
            ← Real.rpow_mul_natCast haR.le]
          have : α * ((2 ^ d : ℕ) : ℝ) = 1 := by
            rw [hα]; push_cast; rw [← mul_pow]; norm_num
          rw [this, Real.rpow_one]
        rw [h2B] at hle
        linarith
  -- small pairs
  set K := ⌊X⌋₊ with hK
  have hsmall : Small ⊆ (Finset.Icc 1 K) ×ˢ (Finset.Icc 1 K) := by
    intro ab hab
    rw [Finset.mem_filter] at hab
    obtain ⟨hbox, hs⟩ := hab
    obtain ⟨⟨ha2, haN⟩, ⟨hb2, hbN⟩, hba⟩ := mem_box.1 hbox
    have haR : (0 : ℝ) < ab.1 := by exact_mod_cast (by omega : 0 < ab.1)
    have haX : (ab.1 : ℝ) ≤ X := by
      have hsplit : (ab.1 : ℝ) = (ab.1 : ℝ) ^ α * (ab.1 : ℝ) ^ (1 - α) := by
        rw [← Real.rpow_add haR]; simp
      have h1 : (ab.1 : ℝ) ^ (1 - α) ≤ (N : ℝ) ^ (1 - α) :=
        Real.rpow_le_rpow haR.le (by exact_mod_cast haN) (by linarith)
      have h2 : (0 : ℝ) ≤ (ab.1 : ℝ) ^ (1 - α) := by positivity
      rw [hsplit, hX]; nlinarith
    have haK : ab.1 ≤ K := Nat.le_floor haX
    simp only [Finset.mem_product, Finset.mem_Icc]
    omega
  have hcardSmall : (Small.card : ℝ) ≤ 4 * (N : ℝ) ^ (2 - α) := by
    have h1 := Finset.card_le_card hsmall
    rw [Finset.card_product, Nat.card_Icc] at h1
    have hKX : (K : ℝ) ≤ X := Nat.floor_le (by linarith)
    have hK0 : (0 : ℝ) ≤ K := by positivity
    have h2 : ((Small.card : ℕ) : ℝ) ≤ X * X := by
      calc ((Small.card : ℕ) : ℝ) ≤ ((K + 1 - 1) * (K + 1 - 1) : ℕ) := by exact_mod_cast h1
        _ = (K : ℝ) * K := by simp
        _ ≤ X * X := by gcongr
    have h3 : X * X ≤ 4 * (N : ℝ) ^ (2 - α) := by
      have : (N : ℝ) ^ (1 - α) * (N : ℝ) ^ (1 - α) ≤ (N : ℝ) ^ (2 - α) := by
        rw [← Real.rpow_add hN0]
        exact Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
      rw [hX]; nlinarith
    linarith
  have hcardIrr := card_irr_le N X hX1 hXN
  have hlogX : Real.log X ≤ 1 + Real.log N := by
    have : Real.log X ≤ Real.log (2 * N) := Real.log_le_log (by linarith) hXN
    rw [Real.log_mul (by norm_num) hN0.ne'] at this
    have := Real.log_two_lt_d9
    linarith
  have hXNeq : 18 * X * N = 36 * (N : ℝ) ^ (2 - α) := by
    rw [hX, show (2 : ℝ) - α = (1 - α) + 1 by ring, Real.rpow_add hN0, Real.rpow_one]; ring
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNR
  have hpow0 : 0 ≤ (N : ℝ) ^ (2 - α) := by positivity
  calc (((ShapeCount.box N).filter (fun ab : ℕ × ℕ => Within ab.1 ab.2 d)).card : ℝ)
      ≤ ((Small ∪ (ShapeCount.box N).filter (fun ab : ℕ × ℕ => Irr X ab.1 ab.2)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsplit
    _ ≤ (Small.card : ℝ) +
        (((ShapeCount.box N).filter (fun ab : ℕ × ℕ => Irr X ab.1 ab.2)).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ 4 * (N : ℝ) ^ (2 - α) + 18 * X * N * (1 + Real.log X) := by linarith
    _ ≤ 4 * (N : ℝ) ^ (2 - α) + 36 * (N : ℝ) ^ (2 - α) * (2 + Real.log N) := by
        rw [hXNeq]
        have : 1 + Real.log X ≤ 2 + Real.log N := by linarith
        have h36 : (0 : ℝ) ≤ 36 * (N : ℝ) ^ (2 - α) := by positivity
        nlinarith
    _ ≤ 40 * (2 + Real.log N) * (N : ℝ) ^ (2 - α) := by nlinarith

/-- The almost-all bound for `D`, on coprime pairs. -/
theorem card_D_le (N d : ℕ) (hN : 1 ≤ N) :
    (((ShapeCount.box N).filter
        (fun ab : ℕ × ℕ => Nat.Coprime ab.1 ab.2 ∧ D ab.1 ab.2 ≤ d)).card : ℝ) ≤
      40 * (2 + Real.log N) * (N : ℝ) ^ (2 - (1 / 2 : ℝ) ^ d) := by
  refine le_trans ?_ (card_within_le N d hN)
  exact_mod_cast Finset.card_le_card (fun ab hab => by
    rw [Finset.mem_filter] at hab ⊢
    exact ⟨hab.1, within_of_D_le hab.2.1 hab.2.2⟩)

/-! ## The almost-all `log log` lower bound -/

open Filter Topology in
theorem tendsto_decay {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun y : ℝ => (2 + Real.log 2 * y) * Real.exp (-Real.log 2 * y ^ ε))
      atTop (𝓝 0) := by
  have hb : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h0 := _root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (Real.log 2) hb
  have h1 := _root_.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / ε) (Real.log 2) hb
  have hsum := (h0.const_mul 2).add (h1.const_mul (Real.log 2))
  rw [mul_zero, mul_zero, add_zero] at hsum
  have hcomp := hsum.comp (tendsto_rpow_atTop hε)
  refine Tendsto.congr' ?_ hcomp
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  simp only [Function.comp]
  rw [Real.rpow_zero, ← Real.rpow_mul hy, mul_one_div_cancel hε.ne', Real.rpow_one]
  ring

open Filter Topology in
/-- **Almost all pairs need `(1 − ε) log₂ log₂ N` steps.** -/
theorem tendsto_card_within_loglog {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Tendsto (fun N : ℕ => (((ShapeCount.box N).filter (fun ab : ℕ × ℕ =>
      Within ab.1 ab.2 ⌊(1 - ε) * Real.logb 2 (Real.logb 2 N)⌋₊)).card : ℝ) / (N : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hy : Tendsto (fun N : ℕ => Real.logb 2 (N : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop
  have hg := ((tendsto_decay hε).comp hy).const_mul 40
  rw [mul_zero] at hg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ?_ ?_
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_ge_atTop 4] with N hN
    simp only [Function.comp]
    have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    set y := Real.logb 2 (N : ℝ) with hydef
    have hy2 : 2 ≤ y := by
      rw [hydef, Real.le_logb_iff_rpow_le one_lt_two hN0]; norm_num; linarith
    have hy0 : 0 < y := by linarith
    set L := Real.logb 2 y with hLdef
    have hL1 : 1 ≤ L := by
      rw [hLdef, Real.le_logb_iff_rpow_le one_lt_two hy0]; norm_num; linarith
    set d := ⌊(1 - ε) * L⌋₊ with hddef
    have hd : (d : ℝ) ≤ (1 - ε) * L := Nat.floor_le (by nlinarith)
    have h2d : (2 : ℝ) ^ d ≤ y ^ (1 - ε) := by
      rw [← Real.rpow_natCast]
      calc (2 : ℝ) ^ (d : ℝ) ≤ (2 : ℝ) ^ ((1 - ε) * L) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hd
        _ = ((2 : ℝ) ^ L) ^ (1 - ε) := by rw [mul_comm, Real.rpow_mul (by norm_num)]
        _ = y ^ (1 - ε) := by rw [hLdef, Real.rpow_logb (by norm_num) (by norm_num) hy0]
    set α : ℝ := (1 / 2 : ℝ) ^ d with hα
    have hαy : y ^ (ε - 1) ≤ α := by
      have hpos : (0 : ℝ) < 2 ^ d := by positivity
      rw [hα, one_div_pow, Real.rpow_sub hy0, Real.rpow_one]
      rw [div_le_div_iff₀ (by positivity) hpos]
      have : y ^ ε * 2 ^ d ≤ y ^ ε * y ^ (1 - ε) := by gcongr
      calc y ^ ε * 2 ^ d ≤ y ^ ε * y ^ (1 - ε) := this
        _ = 1 * y := by rw [← Real.rpow_add hy0]; simp
    have hlogN : Real.log N = Real.log 2 * y := by
      rw [hydef, Real.logb, mul_div_cancel₀ _ hl2.ne']
    have hmain := card_within_le N d (by omega)
    have hNa : (N : ℝ) ^ (2 - α) = (N : ℝ) ^ 2 * (N : ℝ) ^ (-α) := by
      rw [sub_eq_add_neg, Real.rpow_add hN0]; norm_cast
    have hNneg : (N : ℝ) ^ (-α) ≤ Real.exp (-Real.log 2 * y ^ ε) := by
      rw [Real.rpow_def_of_pos hN0, hlogN]
      apply Real.exp_le_exp.2
      have : y * y ^ (ε - 1) = y ^ ε := by
        rw [Real.rpow_sub hy0, Real.rpow_one]; field_simp
      have h1 : Real.log 2 * y * y ^ (ε - 1) ≤ Real.log 2 * y * α := by
        apply mul_le_mul_of_nonneg_left hαy; positivity
      nlinarith
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hN2]
    calc _ ≤ 40 * (2 + Real.log N) * (N : ℝ) ^ (2 - α) := hmain
      _ = 40 * (2 + Real.log 2 * y) * (N : ℝ) ^ (-α) * (N : ℝ) ^ 2 := by
          rw [hNa, hlogN]; ring
      _ ≤ 40 * ((2 + Real.log 2 * y) * Real.exp (-Real.log 2 * y ^ ε)) * (N : ℝ) ^ 2 := by
          have : (0 : ℝ) ≤ 2 + Real.log 2 * y := by positivity
          have h40 : 0 ≤ 40 * (2 + Real.log 2 * y) := by positivity
          calc 40 * (2 + Real.log 2 * y) * (N : ℝ) ^ (-α) * (N : ℝ) ^ 2
              ≤ 40 * (2 + Real.log 2 * y) * Real.exp (-Real.log 2 * y ^ ε) * (N : ℝ) ^ 2 := by
                gcongr
            _ = _ := by ring

end ShortGCD.AlmostAll
