module

public import ShortGCD.Derivation

@[expose] public section

/-! Fixed-width, stack-free remainder generation and its verified acceptance.
The relations in this file deliberately have no nested computation rule.
The two original inputs are retained for final verification; work registers
contain only copies of inputs and remainder results. Costs count remainders.
-/
namespace ShortGCD.TailProgram

abbrev Registers (width : ℕ) := Fin width → ℕ

/-- Stack-free generator runs: return, one remainder assignment, or routing.
There is no nested-call constructor. Routing names a fixed finite set of bodies. -/
inductive Run {width : ℕ} : Registers width → ℕ → ℕ → Prop
  | ret (r : Registers width) (i : Fin width) : Run r 0 (r i)
  | mod {r : Registers width} (i j dest : Fin width) (hp : 0 < r j)
      {n z : ℕ} : Run (Function.update r dest (r i % r j)) n z → Run r (n+1) z
  | route {r : Registers width} (f : Fin width → Fin width) {n z : ℕ} :
      Run (r ∘ f) n z → Run r n z

/-- Every generated value is divisible by every common divisor of the inputs. -/
theorem Run.dvd {width n z d : ℕ} {r : Registers width} (h : Run r n z)
    (hd : ∀ i, d ∣ r i) : d ∣ z := by
  induction h with
  | ret r i => exact hd i
  | mod i j dest hp h ih =>
      apply ih
      intro k
      by_cases hk : k = dest
      · subst k
        simp only [Function.update_self]
        exact (Nat.dvd_mod_iff (hd j)).mpr (hd i)
      · simpa [Function.update_of_ne hk] using hd k
  | route f h ih => exact ih (fun i => hd (f i))
/-- Positive scaling preserves the same choices and remainder count. -/
theorem Run.scale {width n z : ℕ} {r : Registers width} (h : Run r n z)
    {g : ℕ} (hg : 0 < g) : Run (fun i => g*r i) n (g*z) := by
  induction h with
  | ret r i => exact .ret _ i
  | mod i j dest hp h ih =>
      apply Run.mod i j dest (Nat.mul_pos hg hp)
      convert ih using 1
      funext k
      by_cases hk : k = dest
      · subst k; simp [Nat.mul_mod_mul_left]
      · simp [Function.update_of_ne hk]
  | route f h ih => exact .route f ih
/-- Two inputs are duplicated to fill the fixed argument tuple. -/
def inputs (width a b : ℕ) : Registers width := fun i => if i.val = 1 then b else a

/-- The outer program handles a zero second input immediately or verifies a
positive candidate with two remainder calls. Other branches do not converge. -/
inductive Accepts (width : ℕ) : ℕ → ℕ → ℕ → ℕ → Prop
  | zero (a : ℕ) : Accepts width a 0 0 a
  | checked {a b n g : ℕ} (hb : 0 < b) (h : Run (inputs width a b) n g)
      (hg : 0 < g) (ha : a % g = 0) (hbmod : b % g = 0) :
      Accepts width a b (n+2) g

/-- Every accepted computation returns the gcd, regardless of choices. -/
theorem Accepts.correct {width a b n g : ℕ} (h : Accepts width a b n g) :
    g = Nat.gcd a b := by
  cases h with
  | zero => simp
  | checked hb h hg ha hbmod =>
      apply Nat.dvd_antisymm
      · exact Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero ha) (Nat.dvd_of_mod_eq_zero hbmod)
      · apply h.dvd
        intro i
        simp only [inputs]
        split
        · exact Nat.gcd_dvd_right _ _
        · exact Nat.gcd_dvd_left _ _

/-- Euclid gives a successful choice sequence whenever there are at least two registers;
this existence proof is independent of the cost analysis. -/
theorem exists_run_gcd {width : ℕ} (hw : 2 ≤ width) (a b : ℕ) :
    ∃ n, Run (inputs width a b) n (Nat.gcd a b) := by
  let i₀ : Fin width := ⟨0, by omega⟩
  let i₁ : Fin width := ⟨1, by omega⟩
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      by_cases hb : b = 0
      · subst b
        exact ⟨0, by simpa [inputs, i₀] using Run.ret (inputs width a 0) i₀⟩
      have hbpos : 0 < b := by omega
      obtain ⟨n, hrun⟩ := ih (a % b) (Nat.mod_lt a hbpos) b
      let f : Fin width → Fin width := fun i => if i.val = 1 then i₀ else i₁
      have he : (Function.update (inputs width a b) i₀ (a % b)) ∘ f =
          inputs width b (a % b) := by
        funext i
        by_cases hi : i.val = 1
        · simp [f, hi, inputs, i₀]
        · simp [f, hi, inputs, i₀, i₁, Function.update_of_ne]
      have hr : Run (Function.update (inputs width a b) i₀ (a % b)) n
          (Nat.gcd b (a % b)) := Run.route f (he ▸ hrun)
      have hg : Nat.gcd b (a % b) = Nat.gcd a b := by
        rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm b a]
      refine ⟨n+1, ?_⟩
      rw [← hg]
      simpa [inputs, i₀, i₁] using Run.mod i₀ i₁ i₀
        (by simpa [inputs, i₁] using hbpos) hr

/-- The full program has a successful computation on every input. -/
theorem exists_accepts {width : ℕ} (hw : 2 ≤ width) (a b : ℕ) :
    ∃ n, Accepts width a b n (Nat.gcd a b) := by
  by_cases hb : b = 0
  · subst b
    exact ⟨0, by simpa using Accepts.zero (width := width) a⟩
  have hbpos : 0 < b := by omega
  obtain ⟨n, hn⟩ := exists_run_gcd hw a b
  exact ⟨n+2, .checked hbpos hn (Nat.gcd_pos_of_pos_right a hbpos)
    (Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left a b))
    (Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right a b))⟩

/-- `Computes r K z`: some generator run from the registers `r` returns `z` with at most `K`
remainder calls. -/
def Computes {w : ℕ} (r : Registers w) (K z : ℕ) : Prop :=
  ∃ n, n ≤ K ∧ Run r n z

theorem Computes.mono {w K L z} {r : Registers w}
    (h : Computes r K z) (hKL : K ≤ L) : Computes r L z := by
  obtain ⟨n, hn, hr⟩ := h
  exact ⟨n, hn.trans hKL, hr⟩

theorem Computes.ret {w K} (r : Registers w) (i : Fin w) : Computes r K (r i) :=
  ⟨0, Nat.zero_le _, .ret r i⟩

theorem Computes.route {w K z} {r : Registers w} (f : Fin w → Fin w)
    (h : Computes (r ∘ f) K z) : Computes r K z := by
  obtain ⟨n, hn, hr⟩ := h
  exact ⟨n, hn, .route f hr⟩

theorem Computes.pair {w a b K z} {r : Registers w} (i j : Fin w)
    (hi : r i = a) (hj : r j = b) (h : Computes (inputs w a b) K z) :
    Computes r K z := by
  apply Computes.route (fun k => if k.val = 1 then j else i)
  convert h using 1
  funext k
  by_cases hk : k.val = 1 <;> simp [inputs, hk, hi, hj]

theorem Computes.scale {w K z g} {r : Registers w} (h : Computes r K z)
    (hg : 0 < g) : Computes (fun i => g*r i) K (g*z) := by
  obtain ⟨n, hn, hr⟩ := h
  exact ⟨n, hn, hr.scale hg⟩

/-- Multi-step register transformations, interpreted by the generator equations. The index is
an upper bound on the remainder calls (`mono` allows slack). -/
inductive Exec {w : ℕ} : Registers w → ℕ → Registers w → Prop
  | refl (r) : Exec r 0 r
  | mod (r) (i j d : Fin w) (hp : 0 < r j) :
      Exec r 1 (Function.update r d (r i % r j))
  | route (r) (f : Fin w → Fin w) : Exec r 0 (r ∘ f)
  | trans {r s t K L} : Exec r K s → Exec s L t → Exec r (K+L) t
  | mono {r s K L} : Exec r K s → K ≤ L → Exec r L s

theorem Exec.then_compute {w K L z} {r s : Registers w}
    (h : Exec r K s) (hc : Computes s L z) : Computes r (K+L) z := by
  induction h generalizing L with
  | refl => simpa using hc
  | mod r i j d hp =>
      obtain ⟨n, hn, hr⟩ := hc
      exact ⟨n+1, by omega, .mod i j d hp hr⟩
  | route r f => simpa using hc.route f
  | trans h₁ h₂ ih₁ ih₂ =>
      simpa [Nat.add_assoc] using ih₁ (ih₂ hc)
  | mono h hKL ih => exact (ih hc).mono (by omega)

theorem Exec.finish {w K} {r s : Registers w} (h : Exec r K s) (i : Fin w) :
    Computes r K (s i) := by
  simpa using h.then_compute (Computes.ret (K := 0) s i)

/-- `cost w a b`: the least number of remainder calls in a generator run of width `w`
producing `gcd(a, b)` from the inputs (`0` if `w < 2`). -/
noncomputable def cost (w a b : ℕ) : ℕ := by
  classical
  exact if hw : 2 ≤ w then Nat.find (exists_run_gcd hw a b) else 0

theorem computes_cost {w} (hw : 2 ≤ w) (a b : ℕ) :
    Computes (inputs w a b) (cost w a b) (Nat.gcd a b) := by
  classical
  simp only [cost, dite_eq_left hw]
  exact ⟨_, le_rfl, Nat.find_spec (exists_run_gcd hw a b)⟩

theorem cost_le {w a b K} (hw : 2 ≤ w)
    (h : Computes (inputs w a b) K (Nat.gcd a b)) : cost w a b ≤ K := by
  obtain ⟨n, hn, hr⟩ := h
  classical
  simp only [cost, dite_eq_left hw]
  exact (Nat.find_min' (exists_run_gcd hw a b) hr).trans hn

/-- `maxCost w A`: the maximum of `cost w a b` over `a, b ≤ A`, the fixed-width analogue of
`sizeCost`. The tail-program profile uses `maxCost w (2^n)`. -/
noncomputable def maxCost (w A : ℕ) : ℕ :=
  (Finset.range (A+1)).sup (fun a => (Finset.range (A+1)).sup (cost w a))

theorem cost_le_maxCost {w a b A} (ha : a ≤ A) (hb : b ≤ A) :
    cost w a b ≤ maxCost w A :=
  Finset.le_sup_of_le (Finset.mem_range.mpr (by omega))
    (Finset.le_sup (Finset.mem_range.mpr (by omega)))

theorem computes_maxCost {w a b A} (hw : 2 ≤ w) (ha : a ≤ A) (hb : b ≤ A) :
    Computes (inputs w a b) (maxCost w A) (Nat.gcd a b) :=
  (computes_cost hw a b).mono (cost_le_maxCost ha hb)

theorem maxCost_le {w A K} (hw : 2 ≤ w)
    (h : ∀ a b, a ≤ A → b ≤ A → Computes (inputs w a b) K (Nat.gcd a b)) :
    maxCost w A ≤ K := by
  apply Finset.sup_le
  intro a ha
  apply Finset.sup_le
  intro b hb
  exact cost_le hw (h a b (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp ha))
    (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hb)))

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


end ShortGCD.TailProgram
