import ShortGCD.RegisterAsymptotic

/-! # Finite first-order syntax for the fixed-width program

The setters are inlined in this presentation. Each program has four internal
function symbols, with arities `w`, `w`, `3`, and `1`. There are finitely many
bodies for each symbol. Terms contain no numeric literals or higher-order data.
Only remainder and the zero test are primitive operations. `Eval` counts
remainder calls in finite call-by-value evaluation trees; internal calls and
zero tests are uncharged. The operational correspondence with the book's
small-step machine is not a re-formalization of that machine.
-/

noncomputable section
namespace ShortGCD.RegisterProgram.Syntax

inductive Fn where
  | pick | gen | accept | loop
  deriving DecidableEq

abbrev Fn.arity (w : ℕ) : Fn → ℕ
  | .pick | .gen => w
  | .accept => 3
  | .loop => 1

inductive Expr (w n : ℕ) where
  | var : Fin n → Expr w n
  | rem : Expr w n → Expr w n → Expr w n
  | iteZero : Expr w n → Expr w n → Expr w n → Expr w n
  | app (f : Fn) : (Fin (f.arity w) → Expr w n) → Expr w n

def pickVars (w : ℕ) : Expr w w := .app .pick Expr.var
def genVars (w : ℕ) : Expr w w := .app .gen Expr.var

def genMod (w : ℕ) (d : Fin w) : Expr w w :=
  .app .gen (Function.update Expr.var d (.rem (pickVars w) (pickVars w)))
def genSub (w : ℕ) (d : Fin w) : Expr w w :=
  .app .gen (Function.update Expr.var d (genVars w))
def genRoute (w : ℕ) : Expr w w := .app .gen (fun _ => pickVars w)

def acceptBody (w : ℕ) : Expr w 3 :=
  let a := Expr.var 0
  let b := Expr.var 1
  let g := Expr.var 2
  let reject := Expr.app .loop (fun _ => g)
  .iteZero g reject (.iteZero (.rem a g) (.iteZero (.rem b g) g reject) reject)

def bodies (w : ℕ) (f : Fn) : Finset (Expr w (f.arity w)) := by
  classical
  exact match f with
  | .pick => Finset.univ.image Expr.var
  | .gen => {pickVars w, genRoute w} ∪ (Finset.univ.image (genMod w)) ∪
      (Finset.univ.image (genSub w))
  | .accept => {acceptBody w}
  | .loop => {.app .loop Expr.var}

/-- All argument evaluations finish before a function body is entered. A sum
counts their primitive calls; the pure language has no shared mutable state. -/
inductive Eval {w : ℕ} : {n : ℕ} → Registers n → Expr w n → ℕ → ℕ → Prop
  | var {n} (r : Registers n) (i : Fin n) : Eval r (.var i) 0 (r i)
  | rem {n} {r : Registers n} {a b : Expr w n} {K L x y}
      (ha : Eval r a K x) (hb : Eval r b L y) (hp : 0 < y) :
      Eval r (.rem a b) (K+L+1) (x%y)
  | zero {n} {r : Registers n} {a b c : Expr w n} {K L z}
      (ha : Eval r a K 0) (hb : Eval r b L z) : Eval r (.iteZero a b c) (K+L) z
  | pos {n} {r : Registers n} {a b c : Expr w n} {K L x z}
      (ha : Eval r a K x) (hp : 0 < x) (hc : Eval r c L z) :
      Eval r (.iteZero a b c) (K+L) z
  | call {n} {r : Registers n} {f : Fn} {args : Fin (f.arity w) → Expr w n}
      {costs values : Fin (f.arity w) → ℕ} {body : Expr w (f.arity w)} {K z}
      (ha : ∀ i, Eval r (args i) (costs i) (values i))
      (hb : body ∈ bodies w f) (hc : Eval values body K z) :
      Eval r (.app f args) ((∑ i, costs i)+K) z

def Invokes (w : ℕ) (f : Fn) (r : Registers (f.arity w)) (K z : ℕ) : Prop :=
  ∃ body ∈ bodies w f, Eval r body K z

lemma invokes_call {w n f K z} {r : Registers n}
    {args : Fin (f.arity w) → Expr w n} {costs values : Fin (f.arity w) → ℕ}
    (ha : ∀ i, Eval r (args i) (costs i) (values i)) (h : Invokes w f values K z) :
    Eval r (.app f args) ((∑ i, costs i)+K) z := by
  classical
  obtain ⟨body, hb, he⟩ := h
  exact .call ha hb he

lemma pick_invokes {w} (r : Registers w) (i : Fin w) : Invokes w .pick r 0 (r i) := by
  classical
  exact ⟨.var i, by simp [bodies], .var r i⟩

lemma eval_pick {w} (r : Registers w) (i : Fin w) : Eval r (pickVars w) 0 (r i) := by
  classical
  simpa [pickVars] using invokes_call (w := w) (f := .pick) (costs := fun _ => 0) (fun j => Eval.var r j) (pick_invokes r i)

lemma invokes_vars {w K z} {r : Registers w} (h : Invokes w .gen r K z) :
    Eval r (genVars w) K z := by
  classical
  simpa [genVars] using invokes_call (w := w) (f := .gen) (costs := fun _ => 0) (fun j => Eval.var r j) h

lemma sum_single_cost {w} (d : Fin w) (n : ℕ) :
    ∑ i, (if i = d then n else 0) = n := by simp

/-- Every fixed-register run compiles to a finite evaluation of the actual
first-order generator equations, preserving its remainder count exactly. -/
theorem run_invokes {w K z} {r : Registers w} (h : Run r K z) : Invokes w .gen r K z := by
  classical
  induction h with
  | ret r i => exact ⟨pickVars w, by simp [bodies], eval_pick r i⟩
  | @mod r i j d hp n z hr ih =>
    refine ⟨genMod w d, by simp [bodies], ?_⟩
    have ha : ∀ x : Fin w,
        Eval r ((Function.update Expr.var d (.rem (pickVars w) (pickVars w))) x)
          (if x = d then 1 else 0) ((Function.update r d (r i % r j)) x) := by
      intro x
      by_cases hx : x = d
      · subst x
        simp only [Function.update_self, ite_true]
        simpa using Eval.rem (eval_pick r i) (eval_pick r j) hp
      · simpa [Function.update_of_ne hx, hx] using Eval.var r x
    simpa [genMod, sum_single_cost, Nat.add_comm] using invokes_call (w := w) (f := .gen) ha ih
  | @route r f n z hr ih =>
    refine ⟨genRoute w, by simp [bodies], ?_⟩
    have ha : ∀ i : Fin w, Eval r (pickVars w) 0 ((r ∘ f) i) := fun i => eval_pick r (f i)
    simpa [genRoute] using invokes_call (w := w) (f := .gen) ha ih
  | @sub r d n m z y h₁ h₂ ih₁ ih₂ =>
    refine ⟨genSub w d, by simp [bodies], ?_⟩
    have ha : ∀ x : Fin w,
        Eval r ((Function.update Expr.var d (genVars w)) x)
          (if x = d then n else 0) ((Function.update r d y) x) := by
      intro x
      by_cases hx : x = d
      · subst x
        simpa using invokes_vars ih₁
      · simpa [Function.update_of_ne hx, hx] using Eval.var r x
    simpa [genSub, sum_single_cost] using invokes_call (w := w) (f := .gen) ha ih₂

/-- Common divisors are preserved by arbitrary convergent term evaluations,
including evaluations not obtained from the constructed witnesses. -/
theorem Eval.dvd {w n K z d} {r : Registers n} {e : Expr w n} (h : Eval r e K z)
    (hd : ∀ i, d ∣ r i) : d ∣ z := by
  classical
  induction h with
  | var r i => exact hd i
  | rem ha hb hp iha ihb => exact (Nat.dvd_mod_iff (ihb hd)).mpr (iha hd)
  | zero ha hb iha ihb => exact ihb hd
  | pos ha hp hc iha ihc => exact ihc hd
  | call ha hb hc iha ihc => exact ihc (fun i => iha i hd)

lemma Eval.var_spec {w n K z} {r : Registers n} {i : Fin n}
    (h : Eval (w := w) r (.var i) K z) : K = 0 ∧ z = r i := by
  classical
  cases h
  exact ⟨rfl, rfl⟩

lemma Eval.rem_vars_spec {w n K z} {r : Registers n} {i j : Fin n}
    (h : Eval (w := w) r (.rem (.var i) (.var j)) K z) :
    K = 1 ∧ z = r i % r j ∧ 0 < r j := by
  classical
  cases h with
  | rem ha hb hp =>
    cases ha
    cases hb
    exact ⟨rfl, rfl, hp⟩

lemma Eval.loop_free {w n K z} {r : Registers n} {e : Expr w n} (h : Eval r e K z) :
    match e with | .app .loop _ => False | _ => True := by
  classical
  induction h with
  | @call n r f args costs values body K z ha hb hc iha ihc =>
    cases f with
    | pick => trivial
    | gen => trivial
    | accept => trivial
    | loop =>
      have he : body = .app .loop Expr.var := by simpa [bodies] using hb
      subst body
      exact ihc
  | _ => trivial

lemma accept_spec {w K z} {r : Registers 3} (h : Invokes w .accept r K z) :
    z = r 2 ∧ 0 < r 2 ∧ r 0 % r 2 = 0 ∧ r 1 % r 2 = 0 := by
  classical
  obtain ⟨body, hb, he⟩ := h
  have hbody : body = acceptBody w := by simpa [bodies] using hb
  subst body
  dsimp [acceptBody] at he
  cases he with
  | zero hg hloop => exact hloop.loop_free.elim
  | pos hg hp hn =>
    have hg' := hg.var_spec
    cases hn with
    | pos ha hp' hloop => exact hloop.loop_free.elim
    | zero ha hn =>
      have ha' := ha.rem_vars_spec
      cases hn with
      | pos hb hp' hloop => exact hloop.loop_free.elim
      | zero hb hz =>
        have hb' := hb.rem_vars_spec
        have hz' := hz.var_spec
        exact ⟨hz'.2, by omega, ha'.2.1.symm, hb'.2.1.symm⟩

/-- A concrete two-argument entry term. The generator tuple duplicates the input
variables; these are syntactic copies, not a runtime array operation. -/
def head (w : ℕ) : Expr w 2 :=
  .iteZero (.var 1) (.var 0)
    (.app .accept ![.var 0, .var 1,
      .app .gen (fun i => if i.val = 1 then .var 1 else .var 0)])

lemma accept_invokes {w a b g} (hg : 0 < g) (ha : a%g = 0) (hb : b%g = 0) :
    Invokes w .accept ![a,b,g] 2 g := by
  classical
  refine ⟨acceptBody w, by simp [bodies], ?_⟩
  have hea : Eval (w := w) ![a,b,g] (.rem (.var 0) (.var 2)) 1 0 := by
    simpa [ha] using Eval.rem (Eval.var ![a,b,g] 0) (Eval.var ![a,b,g] 2) hg
  have heb : Eval (w := w) ![a,b,g] (.rem (.var 1) (.var 2)) 1 0 := by
    simpa [hb] using Eval.rem (Eval.var ![a,b,g] 1) (Eval.var ![a,b,g] 2) hg
  simpa [acceptBody] using Eval.pos (Eval.var ![a,b,g] 2) hg
    (Eval.zero hea (Eval.zero heb (Eval.var ![a,b,g] 2)))

/-- The acceptance wrapper compiles with exactly the same remainder count. -/
theorem accepts_eval {w a b K g} (h : Accepts w a b K g) : Eval ![a,b] (head w) K g := by
  classical
  induction h with
  | zero =>
    simpa [head] using Eval.zero (Eval.var ![a,0] 1) (Eval.var ![a,0] 0)
  | @checked b n g hb hr hg ha hbmod =>
    have hv : ∀ i : Fin w, Eval (w := w) ![a,b]
        (if i.val = 1 then .var 1 else .var 0) 0 (inputs w a b i) := by
      intro i
      by_cases hi : i.val = 1
      · simpa [hi, inputs] using Eval.var ![a,b] 1
      · simpa [hi, inputs] using Eval.var ![a,b] 0
    have hgen : Eval ![a,b] (.app .gen (fun i : Fin w =>
        if i.val = 1 then .var 1 else .var 0)) n g := by
      simpa using invokes_call (w := w) (f := .gen) hv (run_invokes hr)
    have hargs : ∀ i : Fin 3, Eval (w := w) ![a,b]
        (![.var 0, .var 1, .app .gen (fun i : Fin w =>
          if i.val = 1 then .var 1 else .var 0)] i) (![0,0,n] i) (![a,b,g] i) := by
      intro i
      fin_cases i
      · exact Eval.var _ _
      · exact Eval.var _ _
      · exact hgen
    have hc := invokes_call (w := w) (f := .accept) hargs (accept_invokes (w := w) hg ha hbmod)
    have he := Eval.pos (b := .var 0) (Eval.var ![a,b] 1) hb hc
    simpa [head, Fin.sum_univ_succ] using he

/-- Every terminating evaluation of the finite program returns the gcd.
This includes all nondeterministic choices, not just the selected fast runs. -/
theorem eval_head_correct {w a b K z} (h : Eval ![a,b] (head w) K z) : z = Nat.gcd a b := by
  classical
  dsimp [head] at h
  cases h with
  | zero hb ha =>
    have hb' := hb.var_spec
    have ha' := ha.var_spec
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hb' ha'
    have he : b = 0 := by simpa using hb'.2.symm
    simpa [he] using ha'.2
  | pos hb hp he =>
    cases he with
    | @call _ _ _ _ costs values body K z hargs hbody he =>
      have hs := accept_spec (show Invokes w .accept values K z from ⟨body, hbody, he⟩)
      have ha : values 0 = a := by simpa using (hargs 0).var_spec.2
      have hb : values 1 = b := by simpa using (hargs 1).var_spec.2
      have hd : Nat.gcd a b ∣ values 2 := (hargs 2).dvd (by
        intro i
        fin_cases i
        · exact Nat.gcd_dvd_left a b
        · exact Nat.gcd_dvd_right a b)
      rw [hs.1]
      apply Nat.dvd_antisymm
      · apply Nat.dvd_gcd
        · exact Nat.dvd_of_mod_eq_zero (by simpa [ha] using hs.2.2.1)
        · exact Nat.dvd_of_mod_eq_zero (by simpa [hb] using hs.2.2.2)
      · exact hd

/-- Every input has a terminating evaluation of the finite program. -/
theorem eval_head_exists {w} (hw : 2 ≤ w) (a b : ℕ) :
    ∃ K, Eval ![a,b] (head w) K (Nat.gcd a b) := by
  obtain ⟨K, hK⟩ := exists_accepts hw a b
  exact ⟨K, accepts_eval hK⟩

/-- Fully syntactic version of the fixed-program upper bound. -/
theorem eventually_eval_bound {p : ℕ} (hp : 0 < p) {C : ℝ} (hC : 3/(p:ℝ) < C) :
    ∀ᶠ a : ℕ in Filter.atTop, ∀ b, b ≤ a → ∃ n,
      Eval ![a,b] (head (Fixed.width p)) n (Nat.gcd a b) ∧ (n:ℝ) ≤ C*Real.logb 2 a := by
  classical
  filter_upwards [Fixed.eventually_accepts_bound hp hC] with a ha
  intro b hb
  obtain ⟨n, hn, hc⟩ := ha b hb
  exact ⟨n, accepts_eval hn, hc⟩

theorem arbitrarily_small_program {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℕ, 0 < p ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℕ, 1 ≤ b → b ≤ a →
      ∃ n, Eval ![a,b] (head (Fixed.width p)) n (Nat.gcd a b) ∧
        (n:ℝ) ≤ ε*Real.logb 2 a+B := by
  classical
  obtain ⟨p, hp, B, hB, h⟩ := Fixed.arbitrarily_small_coefficient hε
  refine ⟨p, hp, B, hB, ?_⟩
  intro a b hb hab
  obtain ⟨n, hn, hc⟩ := h a b hb hab
  exact ⟨n, accepts_eval hn, hc⟩

end ShortGCD.RegisterProgram.Syntax
