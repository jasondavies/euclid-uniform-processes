module

public import Mathlib

@[expose] public section

/-! # The Euclidean-prefix lemma

Products of Euclidean step matrices (`Transition`) have nonnegative entries, ordered as in
the paper, and determinant `±1`. If `m · r_h > 2a`, these bounds force a determinant built
from two such products to lie strictly between `0` and `m`, so no residue class modulo `m`
contains `r_s, r_t, r_l` with `s + 2 ≤ t < l ≤ h` (`prefix_class_spread`). Hence each
residue class contains at most three of `r_0, …, r_h` (`prefix_class_card_le_three`), and
the prefix has at least `(h+1)/3` residues (`residue_card_three`). `Contraction` turns this
count into a reservoir.
-/

namespace ShortGCD

/-- The four integer entries of a nonempty product of Euclidean step matrices. -/
structure Transition where
  A : ℤ
  B : ℤ
  C : ℤ
  E : ℤ
  Apos : 1 ≤ A
  Bpos : 1 ≤ B
  Cpos : 1 ≤ C
  Epos : 0 ≤ E
  AB : B ≤ A
  AC : C ≤ A
  BE : E ≤ B
  CE : E ≤ C
  determinant : A * E - B * C = -1 ∨ A * E - B * C = 1

def Transition.single (q : ℕ) (hq : 0 < q) : Transition where
  A := q; B := 1; C := 1; E := 0
  Apos := by omega
  Bpos := le_rfl; Cpos := le_rfl; Epos := le_rfl
  AB := by omega
  AC := by omega
  BE := by omega
  CE := by omega
  determinant := by left; ring

def Transition.prepend (q : ℕ) (hq : 0 < q) (M : Transition) : Transition where
  A := q * M.A + M.C
  B := q * M.B + M.E
  C := M.A
  E := M.B
  Apos := by have := M.Apos; have := M.Cpos; nlinarith
  Bpos := by have := M.Bpos; have := M.Epos; nlinarith
  Cpos := M.Apos
  Epos := le_trans (by omega) M.Bpos
  AB := by
    have := M.AB; have := M.CE
    have : 0 ≤ (q : ℤ) := by omega
    nlinarith
  AC := by have := M.Apos; have := M.Cpos; nlinarith
  BE := by have := M.Bpos; have := M.Epos; nlinarith
  CE := M.AB
  determinant := by
    have hid : ((q : ℤ) * M.A + M.C) * M.B -
        ((q : ℤ) * M.B + M.E) * M.A = -(M.A*M.E-M.B*M.C) := by ring
    rw [hid]
    rcases M.determinant with h | h
    · right; omega
    · left; omega

/-- A finite Euclidean segment carries a transition matrix with the required bounds. A
segment of at least two steps has leading entry at least `2`. -/
theorem transition_exists (r q : ℕ → ℕ) (i d : ℕ)
    (hq : ∀ k, i ≤ k → k < i+d+1 → 0 < q k)
    (hr : ∀ k, i ≤ k → k < i+d+1 → r k = q k * r (k+1) + r (k+2)) :
    ∃ M : Transition,
      (r i : ℤ) = M.A*r (i+d+1) + M.B*r (i+d+2) ∧
      (r (i+1) : ℤ) = M.C*r (i+d+1) + M.E*r (i+d+2) ∧
      (1 ≤ d → 2 ≤ M.A) := by
  induction d generalizing i with
  | zero =>
      refine ⟨.single (q i) (hq i le_rfl (by omega)), ?_, ?_, by omega⟩
      · simp only [Transition.single, Nat.add_zero, Int.one_mul]
        exact_mod_cast hr i le_rfl (by omega)
      · simp [Transition.single]
  | succ d ih =>
      obtain ⟨M,h₁,h₂,-⟩ := ih (i+1)
        (fun k hk hk' => hq k (by omega) (by omega))
        (fun k hk hk' => hr k (by omega) (by omega))
      have hqi : (1:ℤ) ≤ q i := by exact_mod_cast hq i le_rfl (by omega)
      refine ⟨M.prepend (q i) (hq i le_rfl (by omega)), ?_, ?_, fun _ => ?_⟩
      · have he : (r i:ℤ) = (q i:ℤ)*r (i+1) + r (i+2) := by
          exact_mod_cast hr i le_rfl (by omega)
        simp only [Transition.prepend]
        have hi₁ : i+1+d+1 = i+(d+1)+1 := by omega
        have hi₂ : i+1+d+2 = i+(d+1)+2 := by omega
        rw [hi₁,hi₂] at h₁ h₂
        rw [he,h₁,h₂]
        ring
      · simpa [Transition.prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₁
      · have := M.Apos; have := M.Cpos
        simp only [Transition.prepend]
        nlinarith

/-- Two vectors whose dot products with a coprime pair vanish modulo `m`: then `m` divides
their determinant. -/
theorem dvd_det_of_dvd {x y m u₁ u₂ v₁ v₂ : ℤ} (hcop : IsCoprime x y)
    (hu : m ∣ u₁*x + u₂*y) (hv : m ∣ v₁*x + v₂*y) : m ∣ u₁*v₂ - u₂*v₁ := by
  have hx : m ∣ (u₁*v₂ - u₂*v₁)*x := by
    convert dvd_sub (dvd_mul_of_dvd_right hu v₂) (dvd_mul_of_dvd_right hv u₂) using 1
    ring
  have hy : m ∣ (u₁*v₂ - u₂*v₁)*y := by
    convert dvd_sub (dvd_mul_of_dvd_right hv u₁) (dvd_mul_of_dvd_right hu v₁) using 1
    ring
  obtain ⟨p,q,hpq⟩ := hcop
  convert dvd_add (dvd_mul_of_dvd_right hx p) (dvd_mul_of_dvd_right hy q) using 1
  calc u₁*v₂ - u₂*v₁ = (u₁*v₂ - u₂*v₁)*(p*x+q*y) := by rw [hpq, mul_one]
       _ = _ := by ring

/-- No residue class modulo `m > 2a/r_h` contains `r_s, r_t, r_l` with `s + 2 ≤ t < l ≤ h`.
In the basis `(r_l, r_{l+1})`, both `r_s - r_l` and `r_t - r_l` have coefficient vectors
whose determinant `D` is divisible by `m`, while `0 < D < m`. -/
theorem prefix_class_spread (r q : ℕ → ℕ) (a h m : ℕ)
    (hbound : ∀ k, k ≤ h → r k ≤ a)
    (hlower : ∀ k, k ≤ h → r h ≤ r k)
    (hcop : ∀ k, k ≤ h → Nat.Coprime (r k) (r (k+1)))
    (hq : ∀ k, k+1 ≤ h → 0 < q k)
    (heq : ∀ k, k+1 ≤ h → r k = q k*r (k+1)+r (k+2))
    (hm : 2*a < m*r h) {s t l : ℕ} (hst : s+2 ≤ t) (htl : t < l) (hl : l ≤ h)
    (hs : r s % m = r l % m) (ht : r t % m = r l % m) : False := by
  obtain ⟨N,hN,-,hNA⟩ := transition_exists r q s (t-s-1)
    (fun k _ hk => hq k (by omega)) (fun k _ hk => heq k (by omega))
  obtain ⟨M,hM₁,hM₂,-⟩ := transition_exists r q t (l-t-1)
    (fun k _ hk => hq k (by omega)) (fun k _ hk => heq k (by omega))
  have e₁ : s+(t-s-1)+1 = t := by omega
  have e₂ : s+(t-s-1)+2 = t+1 := by omega
  have e₃ : t+(l-t-1)+1 = l := by omega
  have e₄ : t+(l-t-1)+2 = l+1 := by omega
  rw [e₁, e₂] at hN
  rw [e₃, e₄] at hM₁ hM₂
  have hNA := hNA (by omega)
  -- coefficients of `r_s` in the basis `(r_l, r_{l+1})`
  obtain ⟨As, hAs⟩ : ∃ As, As = N.A*M.A + N.B*M.C := ⟨_, rfl⟩
  obtain ⟨Bs, hBs⟩ : ∃ Bs, Bs = N.A*M.B + N.B*M.E := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℤ, x = r l := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℤ, y = r (l+1) := ⟨_, rfl⟩
  have hrs : (r s : ℤ) = As*x + Bs*y := by rw [hN, hM₁, hM₂, hAs, hBs, hx, hy]; ring
  have hds : (m:ℤ) ∣ (As-1)*x + Bs*y := by
    have h := Int.modEq_iff_dvd.mp (show (r l : ℤ) % m = (r s : ℤ) % m by exact_mod_cast hs.symm)
    convert h using 1
    rw [hrs, hx]; ring
  have hdt : (m:ℤ) ∣ (M.A-1)*x + M.B*y := by
    have h := Int.modEq_iff_dvd.mp (show (r l : ℤ) % m = (r t : ℤ) % m by exact_mod_cast ht.symm)
    convert h using 1
    rw [hM₁, hx, hy]; ring
  have hcop' : IsCoprime x y := by
    rw [hx, hy]; exact Nat.isCoprime_iff_coprime.mpr (hcop l hl)
  have hD := dvd_det_of_dvd hcop' hds hdt
  have := N.Apos; have := N.Bpos; have := N.AB; have := M.Apos; have := M.Bpos
  have := M.Cpos; have := M.Epos; have := M.AB; have := M.CE
  -- `2 As < m`, since `As r_h ≤ As r_l ≤ r_s ≤ a < m r_h / 2`
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hBs0 : 0 ≤ Bs := by rw [hBs]; positivity
  have hAs1 : 1 ≤ As := by rw [hAs]; nlinarith
  have hsa : (r s : ℤ) ≤ a := by exact_mod_cast hbound s (by omega)
  have hhl : (r h : ℤ) ≤ x := by rw [hx]; exact_mod_cast hlower l hl
  have hrh : (0:ℤ) < r h := by
    rcases Nat.eq_zero_or_pos (r h) with h0 | h0
    · rw [h0] at hm; omega
    · exact_mod_cast h0
  have hm' : (2:ℤ)*a < m*r h := by exact_mod_cast hm
  have hAx : As*x ≤ a := by linarith [mul_nonneg hBs0 hy0]
  have hAm : 2*As < m := by
    have := mul_le_mul_of_nonneg_left hhl (by omega : (0:ℤ) ≤ As)
    exact lt_of_mul_lt_mul_right (by linarith : 2*As*(r h : ℤ) < m*r h) hrh.le
  -- the determinant `D = σ N_B + (N_A - 1) M_B + N_B M_E`, with `σ = -det M = ±1`
  have hDe : (As-1)*M.B - Bs*(M.A-1) =
      N.B*(M.B*M.C - M.A*M.E) + (N.A-1)*M.B + N.B*M.E := by rw [hAs, hBs]; ring
  have h₁ : N.A*M.B ≤ N.A*M.A := mul_le_mul_of_nonneg_left M.AB (by omega)
  have h₂ : N.B*M.E ≤ N.B*M.C := mul_le_mul_of_nonneg_left M.CE (by omega)
  have h₃ : N.B ≤ N.A*M.A := le_trans N.AB (le_mul_of_one_le_right (by omega) M.Apos)
  have h₄ : 1 ≤ N.B*M.C := one_le_mul_of_one_le_of_one_le N.Bpos M.Cpos
  have hpos : 0 < (As-1)*M.B - Bs*(M.A-1) := by
    rw [hDe]
    have p₁ := mul_nonneg (by omega : (0:ℤ) ≤ N.A-1) (by omega : (0:ℤ) ≤ M.B)
    have p₂ := mul_nonneg (by omega : (0:ℤ) ≤ N.B) M.Epos
    rcases M.determinant with hd | hd
    · have hσ : M.B*M.C - M.A*M.E = 1 := by linarith
      rw [hσ]
      linarith
    · have hσ : M.B*M.C - M.A*M.E = -1 := by linarith
      have hE : 1 ≤ M.E := by
        by_contra hE
        have h0 : M.E = 0 := by omega
        rw [h0, mul_zero] at hd
        have := one_le_mul_of_one_le_of_one_le M.Bpos M.Cpos
        linarith
      have p₃ := mul_le_mul_of_nonneg_left hE (by omega : (0:ℤ) ≤ N.B)
      have p₄ := mul_le_mul_of_nonneg_right (by omega : (1:ℤ) ≤ N.A-1) (by omega : (0:ℤ) ≤ M.B)
      rw [hσ]
      linarith
  have hlt : (As-1)*M.B - Bs*(M.A-1) < m := by
    rw [hDe]
    have hσ : M.B*M.C - M.A*M.E ≤ 1 := by
      rcases M.determinant with hd | hd <;> linarith
    have := mul_le_mul_of_nonneg_left hσ (by omega : (0:ℤ) ≤ N.B)
    have : As = N.A*M.A + N.B*M.C := hAs
    linarith
  have := Int.le_of_dvd hpos hD
  omega

/-- **Three values per class.** Modulo every `m > 2a/r_h`, each residue class contains `r_i`
for at most three indices `i ≤ h`. -/
theorem prefix_class_card_le_three (r q : ℕ → ℕ) (a h m : ℕ)
    (hbound : ∀ k, k ≤ h → r k ≤ a)
    (hlower : ∀ k, k ≤ h → r h ≤ r k)
    (hcop : ∀ k, k ≤ h → Nat.Coprime (r k) (r (k+1)))
    (hq : ∀ k, k+1 ≤ h → 0 < q k)
    (heq : ∀ k, k+1 ≤ h → r k = q k*r (k+1)+r (k+2))
    (hm : 2*a < m*r h) (c : ℕ) :
    ((Finset.range (h+1)).filter (fun i => r i % m = c)).card ≤ 3 := by
  set F := (Finset.range (h+1)).filter (fun i => r i % m = c)
  by_contra hF
  have hF : 3 < F.card := by omega
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  set l := F.max' hne
  have hlF : l ∈ F := F.max'_mem hne
  have hF' : 2 < (F.erase l).card := by rw [Finset.card_erase_of_mem hlF]; omega
  have hne' : (F.erase l).Nonempty := Finset.card_pos.mp (by omega)
  set i := (F.erase l).min' hne'
  have hiF : i ∈ F.erase l := (F.erase l).min'_mem hne'
  have hF'' : 1 < ((F.erase l).erase i).card := by
    rw [Finset.card_erase_of_mem hiF]; omega
  have hmem : ∀ x ∈ F, x ≤ h ∧ r x % m = c := fun x hx => by
    obtain ⟨hx, hc⟩ := Finset.mem_filter.mp hx
    exact ⟨by simpa [Nat.lt_succ_iff] using hx, hc⟩
  have key : ∀ j k, j ∈ (F.erase l).erase i → k ∈ (F.erase l).erase i → j < k → False := by
    intro j k hj hk hjk
    obtain ⟨hji, hj⟩ := Finset.mem_erase.mp hj
    obtain ⟨hki, hk⟩ := Finset.mem_erase.mp hk
    have hij : i < j := lt_of_le_of_ne ((F.erase l).min'_le j hj) (Ne.symm hji)
    obtain ⟨hkl, hkF⟩ := Finset.mem_erase.mp hk
    have hkl' : k < l := lt_of_le_of_ne (F.le_max' k hkF) hkl
    have hiF' := (Finset.mem_erase.mp hiF).2
    obtain ⟨-, hci⟩ := hmem i hiF'
    obtain ⟨-, hck⟩ := hmem k hkF
    obtain ⟨hlh, hcl⟩ := hmem l hlF
    exact prefix_class_spread r q a h m hbound hlower hcop hq heq hm (s := i) (t := k) (l := l)
      (by omega) hkl' hlh (by rw [hci, hcl]) (by rw [hck, hcl])
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp hF''
  rcases lt_or_gt_of_ne hjk with h | h
  · exact key j k hj hk h
  · exact key k j hk hj h

/-- The prefix `r_0, …, r_h` therefore has at least `(h+1)/3` residues modulo `m`. -/
theorem residue_card_three (r q : ℕ → ℕ) (a h m : ℕ)
    (hbound : ∀ k, k ≤ h → r k ≤ a)
    (hlower : ∀ k, k ≤ h → r h ≤ r k)
    (hcop : ∀ k, k ≤ h → Nat.Coprime (r k) (r (k+1)))
    (hq : ∀ k, k+1 ≤ h → 0 < q k)
    (heq : ∀ k, k+1 ≤ h → r k = q k*r (k+1)+r (k+2))
    (hm : 2*a < m*r h) :
    h+1 ≤ 3 * ((Finset.range (h+1)).image (fun k => r k % m)).card := by
  simpa using Finset.card_le_mul_card_image (Finset.range (h+1)) 3
    (fun c _ => prefix_class_card_le_three r q a h m hbound hlower hcop hq heq hm c)

end ShortGCD
