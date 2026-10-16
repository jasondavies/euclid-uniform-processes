import Mathlib

namespace ShortGCD

/-- Elementary exponential domination, used to bound the cost of storing the prefix. -/
theorem four_mul_add_three_le_pow {p : ℕ} (hp : 2 ≤ p) : 4*p+3 ≤ 2^(2*p) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
    have he : 2*(p+1) = 2*p+2 := by omega
    rw [he,pow_add]
    norm_num
    omega

/-- Integer parameters for the construction, avoiding rounding issues with real powers. -/
def prefixLength (n : ℕ) := 2^(2*(Nat.log 2 n/4))+1
def contractionCount (n : ℕ) := n/(Nat.log 2 n/4)+1
def earlyBits (n : ℕ) := (3*n+3)/4
def smallBits (n : ℕ) := (n+2)/3

theorem parameter_bounds {n : ℕ} (hj : 32 ≤ Nat.log 2 n) :
    let j := Nat.log 2 n
    let p := j/4
    0 < n ∧ 1 ≤ p ∧ (2^p)^2 < prefixLength n ∧
    2*2^n ≤ 2^(smallBits n)*2^(earlyBits n) ∧
    2^n ≤ 2^(smallBits n)*(2^p)^(contractionCount n) ∧
    (prefixLength n+1)*j ≤ 64*n ∧
    (prefixLength n+3*contractionCount n+2)*j ≤ 64*n ∧
    earlyBits n < n ∧ smallBits n < n ∧
    j-2 ≤ Nat.log 2 (earlyBits n) ∧ j-2 ≤ Nat.log 2 (smallBits n) ∧
    8*earlyBits n ≤ 7*n ∧ 8*(2*smallBits n) ≤ 7*n := by
  dsimp only
  let j := Nat.log 2 n
  let p := j/4
  have hj' : 32 ≤ j := hj
  have hjn : j ≤ n := Nat.log_le_self 2 n
  have hn : 32 ≤ n := hj'.trans hjn
  have hp : 2 ≤ p := by dsimp [p]; omega
  have h4p : 4*p ≤ j := by dsimp [p]; omega
  have hjp : j ≤ 8*p := by dsimp [p]; omega
  have hjexp : j ≤ 2^(2*p) := by
    have hh := four_mul_add_three_le_pow hp
    have : j ≤ 4*p+3 := by dsimp [p]; omega
    omega
  have hexp : 2^(4*p) ≤ n :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ 2) h4p).trans (Nat.pow_log_le_self 2 (by omega))
  have hprefix : prefixLength n*j ≤ 2*n := by
    change (2^(2*p)+1)*j ≤ 2*n
    have hh := Nat.mul_le_mul_left (2^(2*p)+1) hjexp
    have hpow : 2^(2*p)*2^(2*p) = 2^(4*p) := by rw [←pow_add]; congr 1; omega
    have hpowpos : 1 ≤ 2^(2*p) := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hJ : contractionCount n*j ≤ 16*n := by
    change (n/p+1)*j ≤ 16*n
    have hdiv : n/p*p ≤ n := Nat.div_mul_le_self n p
    have hprod := Nat.mul_le_mul_left (n/p+1) hjp
    have hpn : p ≤ n := (Nat.div_le_self j 4).trans hjn
    nlinarith
  have hlog1 : j-2 ≤ Nat.log 2 (earlyBits n) := by
    have hmono := Nat.log_mono_right (b := 2) (show n/2^2 ≤ earlyBits n from by dsimp [earlyBits]; omega)
    rw [Nat.log_div_base_pow] at hmono
    exact hmono
  have hlog2 : j-2 ≤ Nat.log 2 (smallBits n) := by
    have hmono := Nat.log_mono_right (b := 2) (show n/2^2 ≤ smallBits n from by dsimp [smallBits]; omega)
    rw [Nat.log_div_base_pow] at hmono
    exact hmono
  refine ⟨by omega,by omega,?_,?_,?_,?_,?_,?_,?_,hlog1,hlog2,?_,?_⟩
  · change (2^p)^2 < 2^(2*p)+1
    rw [←pow_mul, Nat.mul_comm p 2]
    omega
  · rw [←pow_add]
    have he : n+1 ≤ smallBits n+earlyBits n := by dsimp [smallBits,earlyBits]; omega
    calc 2*2^n = 2^(n+1) := by rw [pow_succ,Nat.mul_comm]
         _ ≤ _ := Nat.pow_le_pow_right (by omega) he
  · have hnJ : n ≤ p*contractionCount n := by
      dsimp [contractionCount,p,j]
      have := Nat.mod_lt n (by omega : 0 < Nat.log 2 n/4)
      have := Nat.mod_add_div n (Nat.log 2 n/4)
      nlinarith
    have hh : 2^n ≤ (2^p)^(contractionCount n) := by
      rw [←pow_mul]
      exact Nat.pow_le_pow_right (by omega) hnJ
    exact hh.trans (Nat.le_mul_of_pos_left _ (by positivity))
  · nlinarith
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
