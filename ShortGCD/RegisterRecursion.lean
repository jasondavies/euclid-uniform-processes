module

public import ShortGCD.RegisterProgram
public import ShortGCD.Recursive

@[expose] public section

/-! # Register programs as tail-recursive programs

The book's reduction of iteration to tail recursion (§2C), for the register programs of
`RegisterProgram`. Each line `l` becomes a function symbol `p_l` of the `k` registers:
- a halt `return t` becomes the body `t`;
- an assignment `uᵢ := t, goto l'` becomes `p_{l'}(u⃗[i := t])`;
- a branching becomes `p_{l'}(u⃗)` or `p_{l''}(u⃗)` for the tests `tt` and `ff`, and the
  zero-test conditional `if uᵢ = 0 then p_{l'}(u⃗) else p_{l''}(u⃗)` for `eq0(uᵢ)`;
- the alternative commands of a line become alternative bodies (§2E).

`eval_iff_halts` proves that evaluations of `p_l(u⃗)` and convergent computations of the
register program from `(l, u⃗)` correspond exactly, with the same value and remainder cost;
the head may initialise the registers by any map of variables, as in (2F-1).
`compile_tailRecursive` certifies that every call is a tail call, and `stacks_bounded`
bounds the stacks of the book's recursive machine by `2k + 4` on every computation.
-/

namespace ShortGCD.Register
open Recursive

variable {k : ℕ} {ι : Type}

/-- Every line symbol takes the `k` registers. -/
abbrev arity (k : ℕ) (ι : Type) : ι → ℕ := fun _ => k

/-- Terms of the compiled program over `n` variables. -/
abbrev RExpr (k : ℕ) (ι : Type) (n : ℕ) := Recursive.Expr (arity k ι) n

/-- A term of the register program as an expression in the registers. -/
def Term.toExpr : Term k → RExpr k ι k
  | .reg i => .var i
  | .rem i j => .rem (.var i) (.var j)

/-- A tail call of line `l` on the registers. -/
def jump (l : ι) : RExpr k ι k := .app l (fun x => .var x)

/-- The body for one command. -/
def Cmd.toExpr : Cmd k ι → RExpr k ι k
  | .assign i t l => .app l (fun x => if x = i then t.toExpr else .var x)
  | .branch .tt l _ => jump l
  | .branch .ff _ l' => jump l'
  | .branch (.eq0 i) l l' => .iteZero (.var i) (jump l) (jump l')

/-- The bodies of the symbol of line `l`. -/
def compile (P : ι → Line k ι) (l : ι) : Set (RExpr k ι (arity k ι l)) :=
  match P l with
  | .halt t => {t.toExpr}
  | .cmds cs => {e | ∃ c ∈ cs, c.toExpr = e}

/-- The head: call line `l` with register `x` initialised to the variable `σ x`. -/
def head {n : ℕ} (l : ι) (σ : Fin k → Fin n) : RExpr k ι n := .app l (fun x => .var (σ x))

variable (P : ι → Line k ι)

/-! ## Evaluation of terms and arguments -/

lemma term_eval {u : Fin k → ℕ} {t : Term k} {K v : ℕ} :
    Eval (compile P) u (t.toExpr (ι := ι)) K v ↔ t.value u = some v ∧ K = t.calls := by
  cases t with
  | reg i =>
    constructor
    · intro h; obtain ⟨rfl, rfl⟩ := h.var_spec; simp [Term.value, Term.calls]
    · rintro ⟨hv, rfl⟩
      simp only [Term.value, Option.some.injEq] at hv
      subst hv; exact Eval.var u i
  | rem i j =>
    constructor
    · intro h
      obtain ⟨rfl, rfl, hp⟩ := h.rem_vars_spec
      simp [Term.value, Term.calls, hp.ne']
    · rintro ⟨hv, rfl⟩
      simp only [Term.value] at hv
      split_ifs at hv with hj
      cases hv
      exact Eval.rem (Eval.var u i) (Eval.var u j) (Nat.pos_of_ne_zero hj)

lemma vars_eval {n} {r : Fin n → ℕ} {σ : Fin k → Fin n} {costs values : Fin k → ℕ}
    (h : ∀ x, Eval (compile P) r (.var (σ x)) (costs x) (values x)) :
    (∑ x, costs x) = 0 ∧ values = r ∘ σ := by
  have h' := fun x => (h x).var_spec
  exact ⟨by simp [fun x => (h' x).1], funext fun x => (h' x).2⟩

/-- A call with variable arguments evaluates the chosen body on the selected values. -/
lemma head_eval {n} {r : Fin n → ℕ} {l : ι} {σ : Fin k → Fin n} {K z : ℕ} :
    Eval (compile P) r (head l σ) K z ↔
      ∃ body ∈ compile P l, Eval (compile P) (r ∘ σ) body K z := by
  constructor
  · intro h
    cases h with
    | call ha hb hc =>
      obtain ⟨hs, rfl⟩ := vars_eval P ha
      exact ⟨_, hb, by simpa [hs] using hc⟩
  · rintro ⟨body, hb, he⟩
    have h := Eval.call (B := compile P) (r := r) (f := l) (args := fun x => .var (σ x))
      (costs := fun _ => 0) (values := r ∘ σ) (fun x => Eval.var r (σ x)) hb he
    simpa [head] using h

lemma jump_eval {u : Fin k → ℕ} {l : ι} {K z : ℕ} :
    Eval (compile P) u (jump l) K z ↔ ∃ body ∈ compile P l, Eval (compile P) u body K z :=
  head_eval P (σ := id)

lemma assign_args {u : Fin k → ℕ} {i : Fin k} {t : Term k} {v : ℕ}
    (hv : t.value u = some v) :
    ∀ x, Eval (compile P) u (if x = i then t.toExpr else .var x)
      (if x = i then t.calls else 0) (Function.update u i v x) := by
  intro x
  by_cases hx : x = i
  · subst hx; simpa using (term_eval P).mpr ⟨hv, rfl⟩
  · simpa [hx] using Eval.var (B := compile P) u x

lemma assign_args_inv {u : Fin k → ℕ} {i : Fin k} {t : Term k} {costs values : Fin k → ℕ}
    (h : ∀ x, Eval (compile P) u (if x = i then t.toExpr (ι := ι) else .var x)
      (costs x) (values x)) :
    t.value u = some (values i) ∧ values = Function.update u i (values i) ∧
      (∑ x, costs x) = t.calls := by
  have hi := (term_eval P).mp (by simpa using h i)
  have hx : ∀ x, x ≠ i → costs x = 0 ∧ values x = u x := fun x hx =>
    (by simpa [hx] using h x : Eval (compile P) u (.var x) (costs x) (values x)).var_spec
  refine ⟨hi.1, funext fun x => ?_, ?_⟩
  · by_cases h' : x = i
    · subst h'; simp
    · simp [Function.update_of_ne h', (hx x h').2]
  · rw [Finset.sum_eq_single i (fun x _ h' => (hx x h').1) (by simp), hi.2]

/-! ## Computations give evaluations -/

lemma halts_cons {s t : ι × (Fin k → ℕ)} {c K z : ℕ} (hs : Step P s c t) (ht : Halts P t K z) :
    Halts P s (c+K) z := by
  obtain ⟨l, u, t', c', htr, hl, hv, rfl⟩ := ht
  exact ⟨l, u, t', c+c', .cons hs htr, hl, hv, by omega⟩

/-- Every convergent computation from `(l, u)` is an evaluation of a body of `p_l` on `u`. -/
lemma halts_eval {l : ι} {u : Fin k → ℕ} {K z : ℕ} (h : Halts P (l, u) K z) :
    ∃ body ∈ compile P l, Eval (compile P) u body K z := by
  obtain ⟨le, v, t, c', ht, hl, hv, rfl⟩ := h
  suffices H : ∀ s c', Trace P s c' (le, v) →
      ∃ body ∈ compile P s.1, Eval (compile P) s.2 body (c'+t.calls) z from H _ _ ht
  intro s c' ht
  generalize hend : (le, v) = s' at ht
  induction ht with
  | refl =>
    subst hend
    refine ⟨t.toExpr, by simp [compile, hl], (term_eval P).mpr ⟨hv, by simp⟩⟩
  | @cons s s' s'' c c'' hs _ ih =>
    obtain ⟨body, hb, he⟩ := ih hend
    have hj := (jump_eval P).mpr ⟨body, hb, he⟩
    cases hs with
    | @assign l u cs i t₀ l' v₀ hl' hc hv₀ =>
      refine ⟨(Cmd.assign i t₀ l').toExpr, by simp only [compile, hl']; exact ⟨_, hc, rfl⟩, ?_⟩
      obtain ⟨body', hb', he'⟩ := (jump_eval P).mp hj
      have hcall := Eval.call (assign_args P hv₀) hb' he'
      have hsum : (∑ x : Fin k, if x = i then t₀.calls else 0) = t₀.calls := by simp
      simpa [Cmd.toExpr, hsum, Nat.add_assoc] using hcall
    | @branch l u cs tst l' l'' hl' hc =>
      refine ⟨(Cmd.branch tst l' l'').toExpr, by simp only [compile, hl']; exact ⟨_, hc, rfl⟩, ?_⟩
      cases tst with
      | tt => simpa [Cmd.toExpr, Test.value] using hj
      | ff => simpa [Cmd.toExpr, Test.value] using hj
      | eq0 i =>
        by_cases hi : u i = 0
        · have h0 : Eval (compile P) u (.var i) 0 0 := by simpa [hi] using Eval.var u i
          simpa [Cmd.toExpr, Test.value, hi] using Eval.zero (c := jump l'') h0 hj
        · simp only [Test.value, hi, decide_false, Bool.cond_false] at hj
          simpa [Cmd.toExpr] using
            Eval.pos (b := jump l') (Eval.var u i) (Nat.pos_of_ne_zero hi) hj

/-! ## Evaluations give computations -/

/-- What an evaluation of a compiled expression says about the register program: a call of
`p_f` evaluates arguments and then converges from `f`; a conditional takes the branch
selected by its guard. -/
def Good : {n : ℕ} → (Fin n → ℕ) → RExpr k ι n → ℕ → ℕ → Prop
  | _, r, .app f args, K, z => ∃ costs values : Fin k → ℕ, ∃ L,
      (∀ x, Eval (compile P) r (args x) (costs x) (values x)) ∧ Halts P (f, values) L z ∧
      K = (∑ x, costs x)+L
  | _, r, .iteZero a b c, K, z => ∃ K₁ K₂ x, Eval (compile P) r a K₁ x ∧ K = K₁+K₂ ∧
      (x = 0 → Good r b K₂ z) ∧ (0 < x → Good r c K₂ z)
  | _, _, _, _, _ => True

lemma jump_good {u : Fin k → ℕ} {l : ι} {K z : ℕ} (h : Good P u (jump l) K z) :
    Halts P (l, u) K z := by
  simp only [jump, Good] at h
  obtain ⟨costs, values, L, ha, hh, rfl⟩ := h
  obtain ⟨hs, rfl⟩ := vars_eval P (σ := id) ha
  simpa [hs] using hh

lemma body_halts {l : ι} {u : Fin k → ℕ} {body : RExpr k ι k} {K z : ℕ}
    (hb : body ∈ compile P l) (he : Eval (compile P) u body K z) (hg : Good P u body K z) :
    Halts P (l, u) K z := by
  unfold compile at hb
  cases hP : P l with
  | halt t =>
    rw [hP] at hb
    obtain rfl := hb
    obtain ⟨hv, rfl⟩ := (term_eval P).mp he
    exact ⟨l, u, t, 0, .refl _, hP, hv, by simp⟩
  | cmds cs =>
    rw [hP] at hb
    obtain ⟨c, hc, rfl⟩ := hb
    cases c with
    | assign i t l' =>
      simp only [Cmd.toExpr, Good] at hg
      obtain ⟨costs, values, L, ha, hh, rfl⟩ := hg
      obtain ⟨hv, hval, hsum⟩ := assign_args_inv P ha
      rw [hval] at hh
      simpa [hsum] using halts_cons P (Step.assign hP hc hv) hh
    | branch tst l' l'' =>
      have hs := Step.branch (P := P) (u := u) hP hc
      cases tst with
      | tt => simpa [Test.value] using halts_cons P hs (jump_good P hg)
      | ff => simpa [Test.value] using halts_cons P hs (jump_good P hg)
      | eq0 i =>
        simp only [Cmd.toExpr, Good] at hg
        obtain ⟨K₁, K₂, x, ha, rfl, h0, h1⟩ := hg
        obtain ⟨rfl, rfl⟩ := ha.var_spec
        by_cases hi : u i = 0
        · have hs' : Step P (l, u) 0 (l', u) := by simpa [Test.value, hi] using hs
          simpa using halts_cons P hs' (jump_good P (h0 hi))
        · have hs' : Step P (l, u) 0 (l'', u) := by simpa [Test.value, hi] using hs
          simpa using halts_cons P hs' (jump_good P (h1 (Nat.pos_of_ne_zero hi)))

lemma eval_good {n} {r : Fin n → ℕ} {e : RExpr k ι n} {K z : ℕ}
    (h : Eval (compile P) r e K z) : Good P r e K z := by
  induction h with
  | var => simp [Good]
  | rem => simp [Good]
  | zero ha _ _ ihb =>
    simp only [Good]; exact ⟨_, _, 0, ha, rfl, fun _ => ihb, fun h => absurd h (by omega)⟩
  | pos ha hp _ _ ihc =>
    simp only [Good]; exact ⟨_, _, _, ha, rfl, fun h => absurd h (by omega), fun _ => ihc⟩
  | call ha hb hc _ ihc =>
    simp only [Good]; exact ⟨_, _, _, ha, body_halts P hb hc ihc, rfl⟩

/-! ## The correspondence -/

/-- **Exact correspondence.** Evaluations of the head, which calls `p_l` with register `x`
initialised to the variable `σ x`, are exactly the convergent computations of the register
program from line `l`, with the same value and remainder cost. -/
theorem eval_iff_halts {n} (l : ι) (σ : Fin k → Fin n) (r : Fin n → ℕ) (K z : ℕ) :
    Eval (compile P) r (head l σ) K z ↔ Halts P (l, r ∘ σ) K z := by
  constructor
  · intro h
    have hg := eval_good P h
    simp only [head, Good] at hg
    obtain ⟨costs, values, L, ha, hh, rfl⟩ := hg
    obtain ⟨hs, rfl⟩ := vars_eval P ha
    simpa [hs] using hh
  · intro h
    exact (head_eval P).mpr (halts_eval P h)

/-! ## Tail recursion, finiteness and bounded stacks -/

lemma term_callFree (t : Term k) : (t.toExpr (ι := ι)).CallFree := by
  cases t <;> simp [Term.toExpr, Expr.CallFree]

lemma cmd_tailCalls (c : Cmd k ι) : c.toExpr.TailCalls := by
  cases c with
  | assign i t l =>
    intro x
    by_cases hx : x = i
    · simpa [hx] using term_callFree t
    · simp [hx, Expr.CallFree]
  | branch tst l l' =>
    cases tst <;> simp [Cmd.toExpr, jump, Expr.TailCalls, Expr.CallFree]

/-- Every call of the compiled program is a tail call. -/
theorem compile_tailRecursive {n} (l : ι) (σ : Fin k → Fin n) :
    IsTailRecursive (compile P) (head l σ) := by
  refine ⟨fun _ => trivial, fun f body hb => ?_⟩
  unfold compile at hb
  cases hP : P f with
  | halt t =>
    rw [hP] at hb
    obtain rfl := hb
    cases t <;> simp [Term.toExpr, Expr.TailCalls, Expr.CallFree]
  | cmds cs =>
    rw [hP] at hb
    obtain ⟨c, -, rfl⟩ := hb
    exact cmd_tailCalls c

/-- Each line symbol has finitely many bodies. -/
theorem compile_finite (l : ι) : (compile P l).Finite := by
  unfold compile
  cases P l with
  | halt t => exact Set.finite_singleton _
  | cmds cs =>
    exact (List.finite_toSet (cs.map Cmd.toExpr)).subset fun e ⟨c, hc, he⟩ =>
      List.mem_map.mpr ⟨c, hc, he⟩

lemma jump_size (l : ι) : (jump (k := k) l).size = k+1 := by
  simp [jump, Expr.size, arity]; omega

lemma body_size {l : ι} {body : RExpr k ι k} (hb : body ∈ compile P l) :
    body.size ≤ 2*k+4 := by
  unfold compile at hb
  cases hP : P l with
  | halt t =>
    rw [hP] at hb
    obtain rfl := hb
    cases t <;> simp [Term.toExpr, Expr.size]
  | cmds cs =>
    rw [hP] at hb
    obtain ⟨c, -, rfl⟩ := hb
    cases c with
    | assign i t l' =>
      have ht : (t.toExpr (ι := ι)).size ≤ 3 := by cases t <;> simp [Term.toExpr, Expr.size]
      have hle : ∀ x : Fin k, ((if x = i then t.toExpr else .var x : RExpr k ι k)).size ≤
          1 + if x = i then 2 else 0 := by
        intro x
        by_cases hx : x = i
        · simp only [hx, ite_true]; omega
        · simp [hx, Expr.size]
      have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hle x
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
      show 1 + (∑ x : Fin k, ((if x = i then t.toExpr else .var x : RExpr k ι k)).size) ≤ 2*k+4
      omega
    | branch tst l' l'' =>
      cases tst <;> simp [Cmd.toExpr, Expr.size, jump_size] <;> omega

lemma head_size {n} (l : ι) (σ : Fin k → Fin n) : (head l σ).size = k+1 := by
  simp [head, Expr.size, arity]; omega

/-- **Bounded stacks.** On the book's recursive machine running the compiled program from the
head, the control and value stacks together never hold more than `2k + 4` entries, on any
input and however long the computation runs. -/
theorem stacks_bounded {n} (l : ι) (σ : Fin k → Fin n) {r : Fin n → ℕ} {K}
    {t : Machine.State (arity k ι)}
    (h : Machine.Steps (compile P) ⟨[.eval (.mk r (head l σ))], []⟩ K t) :
    t.control.length + t.values.length ≤ 2*k+4 :=
  Machine.stacks_bounded (compile_tailRecursive P l σ) (by rw [head_size]; omega)
    (fun _ _ hb => body_size P hb) h

end ShortGCD.Register
