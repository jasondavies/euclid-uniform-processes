module

public import ShortGCD.Recursive
public import ShortGCD.TailSource

@[expose] public section

/-! # The register program as a tail-recursive program

The register program of `TailSource` written as a finite nondeterministic recursive program,
one function per line, in the sense of Moschovakis's book (§§2A, 2E): the reduction of
iteration to tail recursion (§2C). The symbol `run` has the two inputs and the `w` work
registers as parameters. Its bodies are `run(u[d := rem(u_i, u_j)])`, one for each choice of
work registers `i, j, d`, and `accept(a, b, u_i)`, one for each work register `i`; every call
of `run` is in tail position. `accept` and `loop` perform and reject the final verification.

`executes_iff_eval` proves that evaluations of the head correspond exactly, with the same
value and remainder cost, to executions of the register program, and `executes_iff_steps`
transfers this to the book's recursive machine. Neither direction uses the cost proofs'
relabelling generator. `program_tailRecursive` certifies syntactically that the head
and every body have only tail-position internal calls.
-/

namespace ShortGCD.TailRecursive
open TailProgram TailSource Recursive

inductive Fn where
  | run | accept | loop
  deriving DecidableEq

/-- `run` takes the inputs `a, b` followed by the `w` work registers. -/
abbrev arity (w : ℕ) : Fn → ℕ
  | .run => 2+w
  | .accept => 3
  | .loop => 1

abbrev Term (w n : ℕ) := Recursive.Expr (arity w) n

/-- Parameter positions of `run`: the inputs, then the work registers. -/
def inA {w} : Fin (2+w) := Fin.castAdd w 0
def inB {w} : Fin (2+w) := Fin.castAdd w 1
def work {w} (k : Fin w) : Fin (2+w) := Fin.natAdd 2 k

/-- The parameters of `run` for inputs `a, b` and work registers `r`. -/
def params {w} (a b : ℕ) (r : Registers w) : Fin (2+w) → ℕ := Fin.append ![a,b] r

@[simp] lemma params_inA {w a b} {r : Registers w} : params a b r inA = a := by
  simp [params, inA, Fin.append_left]
@[simp] lemma params_inB {w a b} {r : Registers w} : params a b r inB = b := by
  simp [params, inB, Fin.append_left]
@[simp] lemma params_work {w a b} {r : Registers w} (k : Fin w) :
    params a b r (work k) = r k := by
  simp [params, work, Fin.append_right]

/-- The arguments of the assignment line: `u_d` is replaced by `rem(u_i, u_j)`. -/
def remArgs (w : ℕ) (i j d : Fin w) (x : Fin (2+w)) : Term w (2+w) :=
  if x = work d then .rem (.var (work i)) (.var (work j)) else .var x

lemma remArgs_self (w : ℕ) (i j d : Fin w) :
    remArgs w i j d (work d) = .rem (.var (work i)) (.var (work j)) := by
  simp [remArgs]

lemma remArgs_ne {w : ℕ} {i j d : Fin w} {x : Fin (2+w)} (hx : x ≠ work d) :
    remArgs w i j d x = .var x := by
  simp [remArgs, hx]

/-- The assignment line `u_d := rem(u_i, u_j)`, followed by a tail call of `run`. -/
def runRem (w : ℕ) (i j d : Fin w) : Term w (2+w) := .app .run (remArgs w i j d)

/-- The verification of the candidate `u_i`. -/
def runAccept (w : ℕ) (i : Fin w) : Term w (2+w) :=
  .app .accept ![.var inA, .var inB, .var (work i)]

def acceptBody (w : ℕ) : Term w 3 :=
  let a := Recursive.Expr.var 0
  let b := Recursive.Expr.var 1
  let g := Recursive.Expr.var 2
  let reject := Recursive.Expr.app (ar := arity w) .loop (fun _ => g)
  .iteZero g reject (.iteZero (.rem a g) (.iteZero (.rem b g) g reject) reject)

def bodies (w : ℕ) : (f : Fn) → Set (Term w (arity w f))
  | .run => Set.range (fun t : Fin w × Fin w × Fin w => runRem w t.1 t.2.1 t.2.2) ∪
      Set.range (runAccept w)
  | .accept => {acceptBody w}
  | .loop => {.app .loop (fun x => .var x)}

/-- The program is finite: three symbols, each with finitely many bodies. -/
theorem bodies_finite (w : ℕ) (f : Fn) : (bodies w f).Finite := by
  cases f with
  | run => exact (Set.finite_range _).union (Set.finite_range _)
  | accept => exact Set.finite_singleton _
  | loop => exact Set.finite_singleton _

/-- The initial work registers duplicate the inputs, as in `TailProgram.inputs`. -/
def initVar (w : ℕ) : Fin (2+w) → Fin 2 :=
  Fin.append (fun i : Fin 2 => i) (fun k : Fin w => if k.val = 1 then 1 else 0)

/-- Head: return `a` if `b = 0`; otherwise call `run` on the inputs and their copies. -/
def head (w : ℕ) : Term w 2 :=
  .iteZero (.var 1) (.var 0) (.app .run (fun x => .var (initVar w x)))

/-- Assignment arguments contain only variables and a primitive remainder. -/
lemma remArgs_callFree (w : ℕ) (i j d : Fin w) (x : Fin (2+w)) :
    (remArgs w i j d x).CallFree := by
  unfold remArgs
  split <;> simp [Recursive.Expr.CallFree]

/-- Every alternative of `run`, `accept` and `loop` has only tail-position calls. -/
theorem bodies_tail (w : ℕ) (f : Fn) (body : Term w (arity w f))
    (hb : body ∈ bodies w f) : body.TailCalls := by
  cases f with
  | run =>
    rcases hb with ⟨⟨i, j, d⟩, rfl⟩ | ⟨i, rfl⟩
    · exact remArgs_callFree w i j d
    · change ∀ x : Fin 3, _
      intro x
      fin_cases x <;> simp [Recursive.Expr.CallFree]
  | accept =>
    have he : body = acceptBody w := hb
    subst body
    simp [acceptBody, Recursive.Expr.TailCalls, Recursive.Expr.CallFree]
  | loop =>
    have he : body = .app .loop (fun x => .var x) := hb
    subst body
    simp [Recursive.Expr.TailCalls, Recursive.Expr.CallFree]

/-- The zero-input head also has only tail-position calls. -/
theorem head_tail (w : ℕ) : (head w).TailCalls := by
  simp [head, Recursive.Expr.TailCalls, Recursive.Expr.CallFree]

/-- Syntactic certification of tail recursion for the complete finite program. -/
theorem program_tailRecursive (w : ℕ) : Recursive.IsTailRecursive (bodies w) (head w) :=
  ⟨head_tail w, bodies_tail w⟩

lemma params_inputs (w a b : ℕ) :
    (fun x => ![a,b] (initVar w x)) = params a b (inputs w a b) := by
  funext x
  refine Fin.addCases (fun i => ?_) (fun k => ?_) x
  · simp [initVar, params, Fin.append_left]
  · by_cases hk : k.val = 1 <;> simp [initVar, params, Fin.append_right, inputs, hk]

lemma params_update {w a b} (r : Registers w) (d : Fin w) (v : ℕ) (x : Fin (2+w))
    (hx : x ≠ work d) : params a b r x = params a b (Function.update r d v) x := by
  revert hx
  refine Fin.addCases (fun i _ => ?_) (fun k hx => ?_) x
  · simp [params, Fin.append_left]
  · have hk : k ≠ d := fun h => hx (by rw [h]; rfl)
    have h1 := params_work (a := a) (b := b) (r := r) k
    have h2 := params_work (a := a) (b := b) (r := Function.update r d v) k
    simp only [work] at h1 h2
    rw [h1, h2, Function.update_of_ne hk]

/-! ## Inversion of evaluations -/

lemma call_inv {w n f K z} {r : Fin n → ℕ} {args : Fin (arity w f) → Term w n}
    (h : Eval (bodies w) r (.app f args) K z) :
    ∃ (costs values : Fin (arity w f) → ℕ) (body : Term w (arity w f)) (L : ℕ),
      (∀ i, Eval (bodies w) r (args i) (costs i) (values i)) ∧ body ∈ bodies w f ∧
      Eval (bodies w) values body L z ∧ K = (∑ i, costs i)+L := by
  cases h with
  | call ha hb hc => exact ⟨_, _, _, _, ha, hb, hc, rfl⟩

lemma loop_free {w n K z} {r : Fin n → ℕ} {e : Term w n}
    (h : Eval (bodies w) r e K z) :
    match e with | .app .loop _ => False | _ => True := by
  induction h with
  | @call n r f args costs values body K z ha hb hc iha ihc =>
    cases f with
    | run => trivial
    | accept => trivial
    | loop =>
      have he : body = .app .loop (fun x => .var x) := by
        simpa only [bodies, Set.mem_singleton_iff] using hb
      subst body
      exact ihc
  | _ => trivial

lemma accept_spec {w K z} {r : Fin 3 → ℕ} {body : Term w 3}
    (hb : body ∈ bodies w .accept) (h : Eval (bodies w) r body K z) :
    z = r 2 ∧ 0 < r 2 ∧ r 0 % r 2 = 0 ∧ r 1 % r 2 = 0 ∧ K = 2 := by
  have hbody : body = acceptBody w := by
    simpa only [bodies, Set.mem_singleton_iff] using hb
  subst body
  dsimp [acceptBody] at h
  cases h with
  | zero hg hloop => exact (loop_free hloop).elim
  | pos hg hp hn =>
    have hg' := hg.var_spec
    cases hn with
    | pos ha hp' hloop => exact (loop_free hloop).elim
    | zero ha hn =>
      have ha' := ha.rem_vars_spec
      cases hn with
      | pos hb hp' hloop => exact (loop_free hloop).elim
      | zero hb hz =>
        have hb' := hb.rem_vars_spec
        have hz' := hz.var_spec
        refine ⟨hz'.2, by omega, ha'.2.1.symm, hb'.2.1.symm, by omega⟩

lemma accept_eval {w a b g} (hg : 0 < g) (ha : a%g = 0) (hb : b%g = 0) :
    Eval (bodies w) ![a,b,g] (acceptBody w) 2 g := by
  have hea : Eval (bodies w) ![a,b,g] (.rem (.var 0) (.var 2)) 1 0 := by
    simpa [ha] using Eval.rem (Eval.var (B := bodies w) ![a,b,g] 0)
      (Eval.var (B := bodies w) ![a,b,g] 2) hg
  have heb : Eval (bodies w) ![a,b,g] (.rem (.var 1) (.var 2)) 1 0 := by
    simpa [hb] using Eval.rem (Eval.var (B := bodies w) ![a,b,g] 1)
      (Eval.var (B := bodies w) ![a,b,g] 2) hg
  simpa [acceptBody] using Eval.pos (Eval.var (B := bodies w) ![a,b,g] 2) hg
    (Eval.zero hea (Eval.zero heb (Eval.var (B := bodies w) ![a,b,g] 2)))

/-! ## The assignment line -/

/-- Evaluating the arguments of `runRem` costs one remainder call and produces the updated
registers. -/
lemma sum_indicator {w : ℕ} (d : Fin w) :
    (∑ x : Fin (2+w), if x = work d then 1 else 0) = 1 := by
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma runRem_args {w a b} (r : Registers w) (i j d : Fin w) (hp : 0 < r j) :
    ∀ x : Fin (2+w), Eval (bodies w) (params a b r) (remArgs w i j d x)
      (if x = work d then 1 else 0)
      (params a b (Function.update r d (r i % r j)) x) := by
  intro x
  by_cases hx : x = work d
  · subst x
    rw [remArgs_self]
    simp only [ite_true]
    have h := Eval.rem (Eval.var (B := bodies w) (params a b r) (work i))
      (Eval.var (B := bodies w) (params a b r) (work j)) (by simpa using hp)
    simpa using h
  · rw [remArgs_ne hx]
    simp only [hx, ite_false]
    rw [← params_update r d (r i % r j) x hx]
    exact Eval.var _ x

lemma runRem_inv {w a b K z} {r : Registers w} {i j d : Fin w}
    (h : Eval (bodies w) (params a b r) (runRem w i j d) K z) :
    0 < r j ∧ ∃ body ∈ bodies w .run, ∃ L,
      Eval (bodies w) (params a b (Function.update r d (r i % r j))) body L z ∧ K = L+1 := by
  classical
  obtain ⟨costs, values, body, L, ha, hb, hc, hK⟩ := call_inv h
  have hd : costs (work d) = 1 ∧ values (work d) = r i % r j ∧ 0 < r j := by
    have h0 := ha (work d)
    rw [remArgs_self] at h0
    simpa using h0.rem_vars_spec
  have hvar : ∀ x : Fin (2+w), x ≠ work d → costs x = 0 ∧ values x = params a b r x := by
    intro x hx
    have h0 := ha x
    rw [remArgs_ne hx] at h0
    exact h0.var_spec
  have hj : 0 < r j := hd.2.2
  have hv : values = params a b (Function.update r d (r i % r j)) := by
    funext x
    by_cases hx : x = work d
    · subst x; simpa using hd.2.1
    · rw [(hvar x hx).2, params_update r d (r i % r j) x hx]
  have hc0 : ∀ x : Fin (2+w), costs x = if x = work d then 1 else 0 := by
    intro x
    by_cases hx : x = work d
    · subst x; simpa using hd.1
    · simpa [hx] using (hvar x hx).1
  have hsum : (∑ x, costs x) = 1 := by
    rw [show costs = fun x => if x = work d then 1 else 0 from funext hc0]
    exact sum_indicator d
  subst hv
  exact ⟨hj, body, hb, L, hc, by omega⟩

/-! ## Register-program traces give evaluations -/

/-- The value, cost and pending work of a register-program state, read as an evaluation. -/
def Reads {w} (a b : ℕ) (s : State w) (c z : ℕ) : Prop :=
  match s.1 with
  | .run => ∃ body ∈ bodies w .run, Eval (bodies w) (params a b s.2) body c z
  | .left i => z = s.2 i ∧ c = 2 ∧ 0 < z ∧ a%z = 0 ∧ b%z = 0
  | .right i => z = s.2 i ∧ c = 1 ∧ 0 < z ∧ b%z = 0
  | .done i => z = s.2 i ∧ c = 0
  | .reject => False

lemma step_reads {w a b c k z} {s t : State w} (h : Step a b s c t)
    (ht : Reads a b t k z) : Reads a b s (c+k) z := by
  cases h with
  | rem r i j d hp =>
    obtain ⟨body, hb, he⟩ := ht
    refine ⟨runRem w i j d, Or.inl ⟨(i, j, d), rfl⟩, ?_⟩
    have h := Eval.call (runRem_args (a := a) (b := b) r i j d hp) hb he
    rw [sum_indicator d] at h
    simpa [runRem, Nat.add_comm] using h
  | choose r i hp =>
    obtain ⟨rfl, rfl, hz, ha, hb⟩ := ht
    refine ⟨runAccept w i, Or.inr ⟨i, rfl⟩, ?_⟩
    have hargs : ∀ x : Fin 3, Eval (bodies w) (params a b r)
        (![.var inA, .var inB, .var (work i)] x) 0 (![a, b, r i] x) := by
      intro x
      fin_cases x
      · simpa using Eval.var (B := bodies w) (params a b r) inA
      · simpa using Eval.var (B := bodies w) (params a b r) inB
      · simpa using Eval.var (B := bodies w) (params a b r) (work i)
    simpa [runAccept] using Eval.call hargs (show acceptBody w ∈ bodies w .accept from rfl)
      (accept_eval hz ha hb)
  | zero => exact ht.elim
  | left_ok r i hp h =>
    obtain ⟨rfl, rfl, hz, hb⟩ := ht
    exact ⟨rfl, rfl, hz, h, hb⟩
  | left_bad => exact ht.elim
  | right_ok r i hp h =>
    obtain ⟨rfl, rfl⟩ := ht
    exact ⟨rfl, rfl, hp, h⟩
  | right_bad => exact ht.elim
  | loop => exact ht.elim

lemma trace_reads {w a b c k z} {s t : State w} (h : Trace a b s c t)
    (ht : Reads a b t k z) : Reads a b s (c+k) z := by
  induction h with
  | refl => simpa using ht
  | cons hs ht' ih => simpa [Nat.add_assoc] using step_reads hs (ih ht)

/-! ## Evaluations give register-program traces -/

lemma eval_trace {w a b} : ∀ K (r : Registers w) z (body : Term w (2+w)),
    body ∈ bodies w .run → Eval (bodies w) (params a b r) body K z →
    ∃ t i, Trace a b (.run, r) K (.done i, t) ∧ t i = z := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro r z body hb he
    rcases hb with ⟨⟨i, j, d⟩, rfl⟩ | ⟨i, rfl⟩
    · obtain ⟨hj, body', hb', L, he', hK⟩ := runRem_inv he
      obtain ⟨t, k, ht, hk⟩ := ih L (by omega) _ z body' hb' he'
      refine ⟨t, k, ?_, hk⟩
      have hs := Trace.cons (Step.rem (a := a) (b := b) r i j d hj) ht
      simpa [hK, Nat.add_comm] using hs
    · obtain ⟨costs, values, body', L, ha, hb', hc, hK⟩ := call_inv he
      have h0 := (show Eval (bodies w) (params a b r) (.var inA) (costs 0) (values 0) by
        simpa [runAccept] using ha 0).var_spec
      have h1 := (show Eval (bodies w) (params a b r) (.var inB) (costs 1) (values 1) by
        simpa [runAccept] using ha 1).var_spec
      have h2 := (show Eval (bodies w) (params a b r) (.var (work i)) (costs 2) (values 2) by
        simpa [runAccept] using ha 2).var_spec
      obtain ⟨hz, hp, hav, hbv, hL⟩ := accept_spec hb' hc
      simp only [params_inA, params_inB, params_work] at h0 h1 h2
      rw [h2.2] at hz hp hav hbv
      rw [h0.2] at hav
      rw [h1.2] at hbv
      have hsum : (∑ x, costs x) = 0 := by simp [Fin.sum_univ_three, h0.1, h1.1, h2.1]
      refine ⟨r, i, ?_, hz.symm⟩
      have htr := Trace.cons (Step.choose (a := a) (b := b) r i hp)
        (Trace.cons (Step.left_ok r i hp hav) (Trace.cons (Step.right_ok r i hp hbv)
          (Trace.refl (a := a) (b := b) (.done i, r))))
      simpa [hK, hsum, hL] using htr

/-! ## Exact-cost correspondence -/

/-- Executions of the register program and evaluations of the recursive program correspond
exactly, with the same value and remainder cost. -/
theorem executes_iff_eval (w a b c z : ℕ) :
    Executes w a b c z ↔ Eval (bodies w) ![a,b] (head w) c z := by
  constructor
  · rintro (⟨hb0, hc0, hza⟩ | ⟨hb, r, i, ht, hz⟩)
    · subst hb0 hc0 hza
      simpa [head] using Eval.zero (c := .app .run (fun x => .var (initVar w x)))
        (Eval.var (B := bodies w) ![z,0] 1) (Eval.var (B := bodies w) ![z,0] 0)
    · obtain ⟨body, hbody, he⟩ := trace_reads (k := 0) (z := z) ht
        (show Reads a b (.done i, r) 0 z from ⟨hz.symm, rfl⟩)
      have hargs : ∀ x : Fin (2+w), Eval (bodies w) ![a,b] (.var (initVar w x)) 0
          (params a b (inputs w a b) x) := by
        intro x
        rw [← params_inputs]
        exact Eval.var _ _
      have hcall := Eval.call hargs hbody (by simpa using he)
      have h := Eval.pos (b := .var 0) (Eval.var (B := bodies w) ![a,b] 1) hb hcall
      simpa [head] using h
  · intro h
    dsimp [head] at h
    cases h with
    | zero hb ha =>
      have hb' := hb.var_spec
      have ha' := ha.var_spec
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hb' ha'
      exact Or.inl ⟨hb'.2.symm, by omega, ha'.2⟩
    | pos hb hp he =>
      have hb' := hb.var_spec
      simp only [Matrix.cons_val_one] at hb'
      obtain ⟨costs, values, body, L, ha, hbody, hc, hK⟩ := call_inv he
      have hv : values = params a b (inputs w a b) := by
        rw [← params_inputs]
        funext x
        exact ((ha x).var_spec).2
      have hsum : (∑ x, costs x) = 0 := by simp [fun x => ((ha x).var_spec).1]
      subst hv
      obtain ⟨t, i, ht, hti⟩ := eval_trace L _ z body hbody hc
      refine Or.inr ⟨by rw [hb'.2] at hp; exact hp, t, i, ?_, hti⟩
      simpa [hb'.1, hK, hsum] using ht

/-- The initial machine state evaluating the head on `a, b`, and the halting state. -/
def start (w a b : ℕ) : Machine.State (arity w) := ⟨[.eval (.mk ![a,b] (head w))], []⟩
def halt (w z : ℕ) : Machine.State (arity w) := ⟨[], [.nat z]⟩

/-- The same correspondence for the book's recursive machine. -/
theorem executes_iff_steps (w a b c z : ℕ) :
    Executes w a b c z ↔ Machine.Steps (bodies w) (start w a b) c (halt w z) :=
  (executes_iff_eval w a b c z).trans Machine.eval_iff_steps

/-- Every halting machine computation returns the gcd. -/
theorem steps_correct {w a b c z} (h : Machine.Steps (bodies w) (start w a b) c (halt w z)) :
    z = Nat.gcd a b :=
  executes_correct ((executes_iff_steps w a b c z).mpr h)

/-- Every input has a halting machine computation. -/
theorem steps_total {w} (hw : 2 ≤ w) (a b : ℕ) :
    ∃ c, Machine.Steps (bodies w) (start w a b) c (halt w (Nat.gcd a b)) := by
  obtain ⟨c, hc⟩ := executes_total hw a b
  exact ⟨c, (executes_iff_steps w a b c _).mp hc⟩

/-- **Arbitrarily small coefficients for recursive programs**: for every `ε > 0` there are
`p > 0` and `B ≥ 0` such that, for all `1 ≤ b ≤ a`, the book's recursive machine running the
fixed tail-recursive program for width `4^p + 5` halts with output `gcd(a, b)` at remainder
cost at most `ε log₂ a + B`. -/
theorem arbitrarily_small_coefficient {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℕ, 0 < p ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℕ, 1 ≤ b → b ≤ a →
      ∃ c, Machine.Steps (bodies (Fixed.width p)) (start (Fixed.width p) a b) c
          (halt (Fixed.width p) (Nat.gcd a b)) ∧
        (c:ℝ) ≤ ε*Real.logb 2 a+B := by
  obtain ⟨p, hp, B, hB, h⟩ := TailSource.arbitrarily_small_coefficient hε
  refine ⟨p, hp, B, hB, fun a b hb hab => ?_⟩
  obtain ⟨c, hc, hbound⟩ := h a b hb hab
  exact ⟨c, (executes_iff_steps _ a b c _).mp hc, hbound⟩

end ShortGCD.TailRecursive
