import ShortGCD.FiniteBound
import ShortGCD.Arithmetic

namespace ShortGCD

/-- Uniform sublogarithmic bound in exact integer form. It includes all gcd
inputs, not only coprime pairs. Integer logarithms avoid singular real-log cases. -/
theorem uniform_bit_bound :
    ∃ C : ℕ, 0 < C ∧ ∀ n, sizeCost (2^n) * Nat.log 2 n ≤ C*n := by
  let B := (Finset.range (2^32)).sup (fun n => sizeCost (2^n)*Nat.log 2 n)
  let C := max 4096 B
  have hC : 4096 ≤ C := le_max_left _ _
  refine ⟨C,by omega,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hj : 32 ≤ Nat.log 2 n
    · obtain ⟨hn,hp,hkh,hthreshold,hpower,ho1,ho2,hearly,hsmall,hlog1,hlog2,hd1,hd2⟩ := parameter_bounds hj
      have hrec := sizeCost_step (A := 2^n) (L := 2^(earlyBits n))
        (M := 2^(smallBits n)) (h := prefixLength n) (k := 2^(Nat.log 2 n/4))
        (J := contractionCount n) (Nat.one_le_pow _ _ (by omega)) (by exact Nat.zero_lt_succ _)
        (Nat.one_le_pow _ _ (by omega)) hkh hthreshold hpower
      have hi1 := ih (earlyBits n) hearly
      have hi2 := ih (smallBits n) hsmall
      have hu1 : sizeCost (2^(earlyBits n))*(Nat.log 2 n-2) ≤ C*earlyBits n :=
        (Nat.mul_le_mul_left _ hlog1).trans hi1
      have hu2 : (2*sizeCost (2^(smallBits n)))*(Nat.log 2 n-2) ≤ C*(2*smallBits n) := by
        have hh := (Nat.mul_le_mul_left _ hlog2).trans hi2
        nlinarith
      have hb1 := absorb hj hC hd1 hu1 ho1
      have hb2 := absorb hj hC hd2 hu2 ho2
      have hh := Nat.mul_le_mul_right (Nat.log 2 n) hrec
      rw [max_mul] at hh
      exact hh.trans (max_le (by simpa [Nat.add_assoc] using hb1) (by simpa [Nat.add_assoc] using hb2))
    · by_cases hn : n = 0
      · simp [hn]
      have hnsmall : n < 2^32 := Nat.lt_pow_of_log_lt (by omega) (by omega)
      have hb : sizeCost (2^n)*Nat.log 2 n ≤ B := Finset.le_sup (f := fun n => sizeCost (2^n)*Nat.log 2 n)
        (s := Finset.range (2^32)) (Finset.mem_range.mpr hnsmall)
      exact (hb.trans (le_max_right _ _)).trans (Nat.le_mul_of_pos_right _ (by omega))

theorem uniform_size_input_bound : ∃ C : ℕ, 0 < C ∧ ∀ a,
    sizeCost a * Nat.log 2 (Nat.clog 2 a) ≤ C * Nat.clog 2 a := by
  obtain ⟨C,hC,hbound⟩ := uniform_bit_bound
  refine ⟨C,hC,?_⟩
  intro a
  have ha : a ≤ 2^(Nat.clog 2 a) := Nat.le_pow_clog (by omega) a
  have hmono : sizeCost a ≤ sizeCost (2^(Nat.clog 2 a)) := by
    apply sizeCost_le
    intro x y hx hy
    exact sizeCost_bound _ x y (hx.trans ha) (hy.trans ha)
  exact (Nat.mul_le_mul_right _ hmono).trans (hbound _)

end ShortGCD
