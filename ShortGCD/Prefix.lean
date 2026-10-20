import Mathlib

/-! # The Euclidean-prefix lemma

Products of Euclidean step matrices (`Transition`) have bounded entries and determinant `±1`,
so none fixes a positive coprime pair modulo an `m` exceeding twice its largest entry.
Hence if `m · r_h > 2a`, the consecutive residue pairs `(r_i mod m, r_{i+1} mod m)`, `i < h`,
are pairwise distinct (`prefix_pairs_distinct`), and the prefix has at least `√h` residues
modulo `m` (`residue_card_sq`). `Contraction` turns this into a reservoir.
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
  determinant : A * E - B * C = -1 ∨
    (A * E - B * C = 1 ∧ 3 ≤ A + E)

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
    rcases M.determinant with h | ⟨h, _⟩
    · right
      refine ⟨by omega, ?_⟩
      have := M.Apos; have := M.Bpos; have := M.Cpos
      nlinarith
    · left; omega

/-- The determinant of M-I is strictly negative and at least -2A. -/
theorem Transition.delta_bounds (M : Transition) :
    let d := (M.A-1)*(M.E-1)-M.B*M.C;
    -2*M.A ≤ d ∧ d < 0 := by
  dsimp
  have := M.Apos; have := M.Epos
  have hEA := M.BE.trans M.AB
  rcases M.determinant with h | ⟨h, ht⟩ <;> constructor <;> nlinarith

/-- Adjugate argument: a primitive vector fixed modulo m forces m to divide det(M-I). -/
theorem fixed_vector_dvd_delta (M : Transition) {x y m : ℤ}
    (hcop : IsCoprime x y)
    (h₁ : m ∣ M.A*x + M.B*y - x)
    (h₂ : m ∣ M.C*x + M.E*y - y) :
    m ∣ (M.A-1)*(M.E-1)-M.B*M.C := by
  let d := (M.A-1)*(M.E-1)-M.B*M.C
  have hx : m ∣ d*x := by
    convert dvd_sub (dvd_mul_of_dvd_right h₁ (M.E-1)) (dvd_mul_of_dvd_right h₂ M.B) using 1
    dsimp [d]
    ring
  have hy : m ∣ d*y := by
    convert dvd_sub (dvd_mul_of_dvd_right h₂ (M.A-1)) (dvd_mul_of_dvd_right h₁ M.C) using 1
    dsimp [d]
    ring
  obtain ⟨u,v,huv⟩ := hcop
  have hh := dvd_add (dvd_mul_of_dvd_right hx u) (dvd_mul_of_dvd_right hy v)
  convert hh using 1
  calc d = d * (u*x+v*y) := by rw [huv, mul_one]
       _ = u*(d*x)+v*(d*y) := by ring

/-- No positive coprime pair can be fixed by a short Euclidean transition modulo
an integer larger than twice its leading entry. -/
theorem Transition.not_fixed (M : Transition) {x y m : ℕ}
    (hcop : Nat.Coprime x y) (hm : 2*M.A < m)
    (h₁ : (m : ℤ) ∣ M.A*x + M.B*y - x)
    (h₂ : (m : ℤ) ∣ M.C*x + M.E*y - y) : False := by
  have hd := fixed_vector_dvd_delta M (show IsCoprime (x:ℤ) (y:ℤ) from by
    exact_mod_cast hcop.isCoprime) h₁ h₂
  have hb := M.delta_bounds
  dsimp at hb
  have hp : (0:ℤ) < m := by have := M.Apos; omega
  have hneg := Int.le_of_dvd (by omega : 0 < -((M.A-1)*(M.E-1)-M.B*M.C))
    (dvd_neg.mpr hd)
  omega

/-- A finite Euclidean segment carries a transition matrix with the required bounds. -/
theorem transition_exists (r q : ℕ → ℕ) (i d : ℕ)
    (hq : ∀ k, i ≤ k → k < i+d+1 → 0 < q k)
    (hr : ∀ k, i ≤ k → k < i+d+1 → r k = q k * r (k+1) + r (k+2)) :
    ∃ M : Transition,
      (r i : ℤ) = M.A*r (i+d+1) + M.B*r (i+d+2) ∧
      (r (i+1) : ℤ) = M.C*r (i+d+1) + M.E*r (i+d+2) := by
  induction d generalizing i with
  | zero =>
      refine ⟨.single (q i) (hq i le_rfl (by omega)), ?_, ?_⟩
      · simp only [Transition.single, Nat.add_zero, Int.one_mul]
        exact_mod_cast hr i le_rfl (by omega)
      · simp [Transition.single]
  | succ d ih =>
      obtain ⟨M,h₁,h₂⟩ := ih (i+1)
        (fun k hk hk' => hq k (by omega) (by omega))
        (fun k hk hk' => hr k (by omega) (by omega))
      refine ⟨M.prepend (q i) (hq i le_rfl (by omega)), ?_, ?_⟩
      · have he : (r i:ℤ) = (q i:ℤ)*r (i+1) + r (i+2) := by
          exact_mod_cast hr i le_rfl (by omega)
        simp only [Transition.prepend]
        have hi₁ : i+1+d+1 = i+(d+1)+1 := by omega
        have hi₂ : i+1+d+2 = i+(d+1)+2 := by omega
        rw [hi₁,hi₂] at h₁ h₂
        rw [he,h₁,h₂]
        ring
      · simpa [Transition.prepend, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₁

/-- Euclidean-prefix lemma, in integer form: m*r_h > 2*a suffices for
pairwise distinct consecutive residue pairs. -/
theorem prefix_pairs_distinct (r q : ℕ → ℕ) (a h m : ℕ)
    (hpos : ∀ k, k ≤ h → 0 < r k)
    (hbound : ∀ k, k ≤ h → r k ≤ a)
    (hlower : ∀ k, k ≤ h → r h ≤ r k)
    (hcop : ∀ k, k < h → Nat.Coprime (r k) (r (k+1)))
    (hq : ∀ k, k+2 ≤ h → 0 < q k)
    (heq : ∀ k, k+2 ≤ h → r k = q k*r (k+1)+r (k+2))
    (hm : 2*a < m*r h) :
    Set.InjOn (fun k => (r k % m, r (k+1) % m)) (Set.Iio h) := by
  have hne : ∀ i j, i < j → j < h →
      (r i % m, r (i+1) % m) ≠ (r j % m, r (j+1) % m) := by
    intro i j hij hj he
    obtain ⟨d,hd⟩ : ∃ d, j = i+d+1 := ⟨j-i-1, by omega⟩
    obtain ⟨M,h₁,h₂⟩ := transition_exists r q i d
      (fun k hk hk' => hq k (by omega))
      (fun k hk hk' => heq k (by omega))
    have he₁ := congrArg Prod.fst he
    have he₂ := congrArg Prod.snd he
    simp only [hd] at he₁ he₂
    have hd₁ : (m:ℤ) ∣ (r i:ℤ) - r (i+d+1) := by
      apply Int.modEq_iff_dvd.mp
      apply Eq.symm
      exact_mod_cast he₁
    have hd₂ : (m:ℤ) ∣ (r (i+1):ℤ) - r (i+d+2) := by
      apply Int.modEq_iff_dvd.mp
      apply Eq.symm
      simpa [Nat.add_assoc] using (show (r (i+1):ℤ) % (m:ℤ) =
        (r (i+d+1+1):ℤ) % (m:ℤ) from by exact_mod_cast he₂)
    have hAj : M.A * (r j:ℤ) ≤ a := by
      have hp : (0:ℤ) ≤ M.B * r (j+1) := mul_nonneg (by have := M.Bpos; omega) (by omega)
      have hu : (r i:ℤ) ≤ a := by exact_mod_cast hbound i (by omega)
      rw [hd] at *
      nlinarith [h₁]
    have hAr : M.A * (r h:ℤ) ≤ a := by
      have hh : (r h:ℤ) ≤ r j := by exact_mod_cast hlower j (by omega)
      have := M.Apos
      nlinarith
    have hm' : (2:ℤ)*a < (m:ℤ)*r h := by exact_mod_cast hm
    have hp' : (0:ℤ) < r h := by exact_mod_cast hpos h le_rfl
    have hAM : 2*M.A < m := by nlinarith
    rw [h₁] at hd₁
    rw [h₂] at hd₂
    exact M.not_fixed (by simpa [hd, Nat.add_assoc] using hcop j hj) hAM hd₁ hd₂
  intro i hi j hj he
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (hne i j hij hj he)
  · exact hij
  · exact False.elim (hne j i hij hi he.symm)

/-- h distinct consecutive residue pairs force at least sqrt(h) distinct residues. -/
theorem residue_card_sq (r : ℕ → ℕ) (h m : ℕ)
    (hinj : Set.InjOn (fun k => (r k % m, r (k+1) % m)) (Set.Iio h)) :
    h ≤ ((Finset.range (h+1)).image (fun k => r k % m)).card ^ 2 := by
  let R := (Finset.range (h+1)).image (fun k => r k % m)
  have hh : (Finset.range h).card ≤ (R ×ˢ R).card :=
    Finset.card_le_card_of_injOn (fun k => (r k % m, r (k+1) % m))
      (by
        intro k hk
        have hk' := Finset.mem_range.mp hk
        exact Finset.mem_product.mpr
          ⟨Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega)),
           Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))⟩)
      (by simpa using hinj)
  simpa [R, pow_two] using hh

end ShortGCD
