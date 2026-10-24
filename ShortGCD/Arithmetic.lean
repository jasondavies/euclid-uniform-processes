module

public import Mathlib

@[expose] public section

/-! # Parameter choices for the uniform bound

Natural-number parameters for `sizeCost_step` at size `2^n`, as in the paper: with
`j = ⌊log₂ n⌋` and `p = ⌊j/2⌋`, a prefix of `h = 3k` steps with `k = 2^p`, `J = ⌈n/p⌉`
contractions of ratio `k`, and recursive sizes `⌈3n/4⌉` and `⌈n/3⌉` bits. `parameter_bounds`
collects the inequalities they satisfy, and `absorb` is the arithmetic step of the induction
in `UpperBound`.
-/

namespace ShortGCD

/-- Elementary exponential domination, used to bound the cost of storing the prefix. -/
theorem four_mul_add_two_le_pow {p : ℕ} (hp : 5 ≤ p) : 4*p+2 ≤ 2^p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
    rw [pow_succ]
    omega

/-- Integer parameters for the construction, avoiding rounding issues with real powers. -/
def prefixLength (n : ℕ) := 3*2^(Nat.log 2 n/2)
def contractionCount (n : ℕ) := (n+Nat.log 2 n/2-1)/(Nat.log 2 n/2)
def earlyBits (n : ℕ) := (3*n+3)/4
def smallBits (n : ℕ) := (n+2)/3

theorem parameter_bounds {n : ℕ} (hj : 32 ≤ Nat.log 2 n) :
    let j := Nat.log 2 n
    let p := j/2
    0 < n ∧ 1 ≤ p ∧ 3*2^p ≤ prefixLength n ∧
    2*2^n ≤ 2^(smallBits n)*2^(earlyBits n) ∧
    2^n ≤ 2^(smallBits n)*(2^p)^(contractionCount n) ∧
    (prefixLength n+1)*j ≤ 64*n ∧
    (prefixLength n+3*contractionCount n+2)*j ≤ 64*n ∧
    earlyBits n < n ∧ smallBits n < n ∧
    j-2 ≤ Nat.log 2 (earlyBits n) ∧ j-2 ≤ Nat.log 2 (smallBits n) ∧
    8*earlyBits n ≤ 7*n ∧ 8*(2*smallBits n) ≤ 7*n := by
  dsimp only
  let j := Nat.log 2 n
  let p := j/2
  have hj' : 32 ≤ j := hj
  have hjn : j ≤ n := Nat.log_le_self 2 n
  have hn : 32 ≤ n := hj'.trans hjn
  have hp : 16 ≤ p := by dsimp [p]; omega
  have h2p : 2*p ≤ j := by dsimp [p]; omega
  have hjp : j ≤ 2*p+1 := by dsimp [p]; omega
  have hexp : 2^p*2^p ≤ n := by
    rw [← pow_add]
    exact (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : p+p ≤ j)).trans
      (Nat.pow_log_le_self 2 (by omega))
  have hprefix : (prefixLength n+1)*j ≤ 2*n := by
    change (3*2^p+1)*j ≤ 2*n
    have hpow := four_mul_add_two_le_pow (by omega : 5 ≤ p)
    have h1 : 1 ≤ 2^p := Nat.one_le_pow _ _ (by omega)
    have hj2 : (3*2^p+1)*j ≤ (4*2^p)*(2*p+1) :=
      Nat.mul_le_mul (by omega) hjp
    calc (3*2^p+1)*j ≤ (4*2^p)*(2*p+1) := hj2
         _ = 2*2^p*(4*p+2) := by ring
         _ ≤ 2*2^p*2^p := Nat.mul_le_mul_left _ hpow
         _ = 2*(2^p*2^p) := by ring
         _ ≤ 2*n := Nat.mul_le_mul_left _ hexp
  have hdiv : contractionCount n*p ≤ n+p-1 := by
    change (n+p-1)/p*p ≤ n+p-1
    exact Nat.div_mul_le_self _ _
  have hnJ : n ≤ p*contractionCount n := by
    change n ≤ p*((n+p-1)/p)
    have h1 := Nat.mod_lt (n+p-1) (by omega : 0 < p)
    have h2 := Nat.mod_add_div (n+p-1) p
    generalize p*((n+p-1)/p) = X at h2 ⊢
    omega
  have hJ : contractionCount n*j ≤ 6*n := by
    calc contractionCount n*j ≤ contractionCount n*(3*p) :=
          Nat.mul_le_mul_left _ (by omega)
         _ = 3*(contractionCount n*p) := by ring
         _ ≤ 3*(n+p-1) := Nat.mul_le_mul_left _ hdiv
         _ ≤ 6*n := by omega
  have hlog1 : j-2 ≤ Nat.log 2 (earlyBits n) := by
    have hmono := Nat.log_mono_right (b := 2) (show n/2^2 ≤ earlyBits n from by dsimp [earlyBits]; omega)
    rw [Nat.log_div_base_pow] at hmono
    exact hmono
  have hlog2 : j-2 ≤ Nat.log 2 (smallBits n) := by
    have hmono := Nat.log_mono_right (b := 2) (show n/2^2 ≤ smallBits n from by dsimp [smallBits]; omega)
    rw [Nat.log_div_base_pow] at hmono
    exact hmono
  refine ⟨by omega,by omega,le_rfl,?_,?_,hprefix.trans (by omega),?_,?_,?_,hlog1,hlog2,?_,?_⟩
  · rw [←pow_add]
    have he : n+1 ≤ smallBits n+earlyBits n := by dsimp [smallBits,earlyBits]; omega
    calc 2*2^n = 2^(n+1) := by rw [pow_succ,Nat.mul_comm]
         _ ≤ _ := Nat.pow_le_pow_right (by omega) he
  · have hh : 2^n ≤ (2^p)^(contractionCount n) := by
      rw [←pow_mul]
      exact Nat.pow_le_pow_right (by omega) hnJ
    exact hh.trans (Nat.le_mul_of_pos_left _ (by positivity))
  · nlinarith
  · dsimp [earlyBits]; omega
  · dsimp [smallBits]; omega
  · dsimp [earlyBits]; omega
  · dsimp [smallBits]; omega

/-- A single arithmetic absorption inequality for either branch of the recurrence. -/
theorem absorb {n j C d U overhead : ℕ}
    (hj : 32 ≤ j) (hC : 4096 ≤ C) (hd : 8*d ≤ 7*n)
    (hU : U*(j-2) ≤ C*d) (ho : overhead*j ≤ 64*n) :
    (overhead+U)*j ≤ C*n := by
  have hratio : 8*j ≤ 9*(j-2) := by omega
  have huj : 8*(U*j) ≤ 9*(C*d) := by
    calc 8*(U*j) = U*(8*j) := by ring
         _ ≤ U*(9*(j-2)) := Nat.mul_le_mul_left U hratio
         _ = 9*(U*(j-2)) := by ring
         _ ≤ 9*(C*d) := Nat.mul_le_mul_left 9 hU
  have huj' : 64*(U*j) ≤ 63*(C*n) := by
    calc 64*(U*j) = 8*(8*(U*j)) := by ring
         _ ≤ 8*(9*(C*d)) := Nat.mul_le_mul_left 8 huj
         _ = 9*C*(8*d) := by ring
         _ ≤ 9*C*(7*n) := Nat.mul_le_mul_left (9*C) hd
         _ = 63*(C*n) := by ring
  have hcn : 4096*n ≤ C*n := Nat.mul_le_mul_right n hC
  nlinarith

end ShortGCD
