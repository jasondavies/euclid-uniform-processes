module

public import ShortGCD.Derivation

@[expose] public section

/-! # A finite-arity nondeterministic generator

`Run` is the big-step semantics of the generator in the paper's section "Fixed
programs with arbitrarily small coefficients", expanded in
research/nondeterministic-prefix.tex. `Registers w` is the
generator's parameter tuple `x₀ … x_{w−1}`. The width is fixed before execution.
Indices and routing functions name finitely many syntactic choices, not
natural-number data available to the program. Only remainder calls are charged.

Arithmetic soundness, homogeneity, and existence of successful computations
are checked here. `RegisterRecurrence` and `RegisterAsymptotic` establish the
program cost bound; `RegisterSyntax` compiles these runs to finite first-order
syntax with call-by-value evaluation trees. `RegisterSmallStep` proves
exact-cost correspondence with the specialized two-stack recursive machine.
-/

namespace ShortGCD.RegisterProgram

/-- The generator's parameter tuple `x₀, …, x_{w−1}`. -/
abbrev Registers (width : ℕ) := Fin width → ℕ

/-- Successful generator computations. The subcall retains the caller's
registers. Routing copies or permutes parameters without arithmetic. -/
inductive Run {width : ℕ} : Registers width → ℕ → ℕ → Prop
  | ret (r : Registers width) (i : Fin width) : Run r 0 (r i)
  | mod {r : Registers width} (i j dest : Fin width) (hp : 0 < r j)
      {n z : ℕ} : Run (Function.update r dest (r i % r j)) n z → Run r (n+1) z
  | route {r : Registers width} (f : Fin width → Fin width) {n z : ℕ} :
      Run (r ∘ f) n z → Run r n z
  | sub {r : Registers width} (dest : Fin width) {n m z y : ℕ} :
      Run r n y → Run (Function.update r dest y) m z → Run r (n+m) z

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
  | sub dest h₁ h₂ ih₁ ih₂ =>
      apply ih₂
      intro k
      by_cases hk : k = dest
      · subst k
        simpa using ih₁ hd
      · simpa [Function.update_of_ne hk] using hd k

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
  | sub dest h₁ h₂ ih₁ ih₂ =>
      apply Run.sub dest ih₁
      convert ih₂ using 1
      funext k
      by_cases hk : k = dest
      · subst k; simp
      · simp [Function.update_of_ne hk]

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

end ShortGCD.RegisterProgram

