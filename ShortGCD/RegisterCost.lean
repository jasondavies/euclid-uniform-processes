module

public import ShortGCD.RegisterPrefix

@[expose] public section

/-! # Elementary bounds on fixed-width costs

At any width `w ≥ 2`: inputs can be swapped, one Euclidean step costs one call, zero and equal
inputs cost nothing, positive scaling preserves costs, and ordinary Euclid gives
`maxCost w (2^n) ≤ 2n` (`maxCost_pow_le`). `RegisterRecurrence` uses these for the recurrence,
and `RegisterAsymptotic` for boundedness of `T_W(n)/n`.
-/

namespace ShortGCD.RegisterProgram

lemma computes_swap {w a b K z} (hw : 2 ≤ w)
    (h : Computes (inputs w b a) K z) : Computes (inputs w a b) K z := by
  exact h.pair (r := inputs w a b) ⟨1, by omega⟩ ⟨0, by omega⟩
    (by simp [inputs]) (by simp [inputs])

lemma computes_euclid {w a b K} (hw : 2 ≤ w) (hb : 0 < b)
    (h : Computes (inputs w b (a%b)) K (Nat.gcd b (a%b))) :
    Computes (inputs w a b) (K+1) (Nat.gcd a b) := by
  let i : Fin w := ⟨0, by omega⟩
  let j : Fin w := ⟨1, by omega⟩
  let r := inputs w a b
  let s := Function.update r i (a%b)
  have he : Exec r 1 s := by
    simpa [r, s, i, j, inputs] using Exec.mod r i j i (by simpa [r, j, inputs] using hb)
  have hc : Computes s K (Nat.gcd b (a%b)) := h.pair j i
    (by simp [s, r, j, i, inputs, Function.update_of_ne]) (by simp [s])
  have hg : Nat.gcd b (a%b) = Nat.gcd a b := by
    rw [Nat.gcd_comm b (a%b), ← Nat.gcd_rec, Nat.gcd_comm b a]
  simpa [hg, Nat.add_comm] using he.then_compute hc

lemma computes_zero {w a K} (hw : 2 ≤ w) :
    Computes (inputs w a 0) K (Nat.gcd a 0) := by
  simpa [inputs] using Computes.ret (K := K) (inputs w a 0) ⟨0, by omega⟩

lemma computes_self {w a K} (hw : 2 ≤ w) :
    Computes (inputs w a a) K (Nat.gcd a a) := by
  simpa [inputs] using Computes.ret (K := K) (inputs w a a) ⟨0, by omega⟩

/-- A coarse logarithmic bound supplied by ordinary Euclid. -/
lemma computes_euclid_bound {w} (hw : 2 ≤ w) (n : ℕ) :
    ∀ a b, b ≤ a → a ≤ 2^n → Computes (inputs w a b) (2*n) (Nat.gcd a b) := by
  induction n with
  | zero =>
    intro a b hab ha
    by_cases hb : b = 0
    · subst b; exact computes_zero hw
    · have he : b = a := by simp only [pow_zero] at ha; omega
      subst b; exact computes_self hw
  | succ n ih =>
    intro a b hab ha
    by_cases hb : b = 0
    · subst b; exact computes_zero hw
    have hbp : 0 < b := by omega
    by_cases hs : b ≤ 2^n
    · exact (computes_euclid hw hbp (ih b (a%b) (Nat.mod_lt _ hbp).le hs)).mono (by omega)
    have hr : a%b ≤ 2^n := by
      rw [Nat.mod_eq_sub_mod hab]
      apply (Nat.mod_le _ _).trans
      rw [pow_succ] at ha
      omega
    by_cases hz : a%b = 0
    · have hh : Computes (inputs w b (a%b)) (2*n) (Nat.gcd b (a%b)) := by
        rw [hz]; exact computes_zero hw
      exact (computes_euclid hw hbp hh).mono (by omega)
    · have hh := computes_euclid hw (show 0 < a%b by omega)
        (ih (a%b) (b%(a%b)) (Nat.mod_lt _ (by omega)).le hr)
      exact (computes_euclid hw hbp hh).mono (by omega)

lemma maxCost_pow_le {w} (hw : 2 ≤ w) (n : ℕ) : maxCost w (2^n) ≤ 2*n := by
  apply maxCost_le hw
  intro a b ha hb
  by_cases hab : b ≤ a
  · exact computes_euclid_bound hw n a b hab ha
  · have hh := computes_euclid_bound hw n b a (by omega) hb
    simpa [Nat.gcd_comm] using computes_swap hw hh

lemma computes_scaled_inputs {w a b K g} (hg : 0 < g)
    (h : Computes (inputs w a b) K (Nat.gcd a b)) :
    Computes (inputs w (g*a) (g*b)) K (Nat.gcd (g*a) (g*b)) := by
  have he : (fun i => g * inputs w a b i) = inputs w (g*a) (g*b) := by
    funext i
    simp only [inputs]
    split <;> rfl
  simpa [he, Nat.gcd_mul_left] using h.scale hg

end ShortGCD.RegisterProgram
