module

public import ShortGCD.RegisterSyntax

@[expose] public section

/-! # The two-stack recursive machine for the fixed finite programs

The control stack is stored with its top at the head (the reverse of the
book's printed left stack). Argument terms are pushed right to left. The
value stack distinguishes individuals and booleans; `eq0` and the subsequent
branch are separate transitions. Only an external remainder transition has
cost one. Closures represent substitution of actual individual values into
source terms, not an extra data type or primitive available to the program.
The rules specialize Moschovakis, *Abstract Recursion and Intrinsic
Complexity* (2019), Table 1, p. 75, with the finite body choices of §2E.
-/

noncomputable section
namespace ShortGCD.RegisterProgram.Syntax.Machine

inductive Closure (w : ℕ) where
  | mk {n : ℕ} (r : Registers n) (e : Expr w n)

inductive Value where
  | nat : ℕ → Value
  | bool : Bool → Value
  deriving DecidableEq

inductive Instr (w : ℕ) where
  | eval : Closure w → Instr w
  | test : Closure w → Instr w
  | rem : Instr w
  | eq0 : Instr w
  | branch : Closure w → Closure w → Instr w
  | call : Fn → Instr w

def arguments {w n : ℕ} (r : Registers n) :
    {k : ℕ} → (Fin k → Expr w n) → List (Instr w)
  | 0, _ => []
  | k+1, args => .eval (.mk r (args (Fin.last k))) ::
      arguments r (fun i => args i.castSucc)

structure State (w : ℕ) where
  control : List (Instr w)
  values : List Value

/-- The specialized transition table: pass, composition, external and internal
calls, and branching. The only nondeterminism is the finite body choice. -/
inductive Step {w : ℕ} : State w → ℕ → State w → Prop
  | var {n} (r : Registers n) (i : Fin n) (cs vs) :
      Step ⟨.eval (.mk r (.var i)) :: cs, vs⟩ 0 ⟨cs, .nat (r i) :: vs⟩
  | compRem {n} (r : Registers n) (a b : Expr w n) (cs vs) :
      Step ⟨.eval (.mk r (.rem a b)) :: cs, vs⟩ 0
        ⟨.eval (.mk r b) :: .eval (.mk r a) :: .rem :: cs, vs⟩
  | compZero {n} (r : Registers n) (a b c : Expr w n) (cs vs) :
      Step ⟨.eval (.mk r (.iteZero a b c)) :: cs, vs⟩ 0
        ⟨.test (.mk r a) :: .branch (.mk r b) (.mk r c) :: cs, vs⟩
  | compTest (a : Closure w) (cs vs) :
      Step ⟨.test a :: cs, vs⟩ 0 ⟨.eval a :: .eq0 :: cs, vs⟩
  | compCall {n} (r : Registers n) (f : Fn) (args : Fin (f.arity w) → Expr w n) (cs vs) :
      Step ⟨.eval (.mk r (.app f args)) :: cs, vs⟩ 0
        ⟨arguments r args ++ .call f :: cs, vs⟩
  | rem (x y : ℕ) (hp : 0 < y) (cs vs) :
      Step ⟨.rem :: cs, .nat x :: .nat y :: vs⟩ 1 ⟨cs, .nat (x%y) :: vs⟩
  | eq0 (x : ℕ) (cs vs) :
      Step ⟨.eq0 :: cs, .nat x :: vs⟩ 0 ⟨cs, .bool (decide (x=0)) :: vs⟩
  | branchTrue (a b : Closure w) (cs vs) :
      Step ⟨.branch a b :: cs, .bool true :: vs⟩ 0 ⟨.eval a :: cs, vs⟩
  | branchFalse (a b : Closure w) (cs vs) :
      Step ⟨.branch a b :: cs, .bool false :: vs⟩ 0 ⟨.eval b :: cs, vs⟩
  | call (f : Fn) (r : Registers (f.arity w)) (body : Expr w (f.arity w))
      (hb : body ∈ bodies w f) (cs vs) :
      Step ⟨.call f :: cs, List.ofFn (fun i => Value.nat (r i)) ++ vs⟩ 0
        ⟨.eval (.mk r body) :: cs, vs⟩

/-- Finite transition sequences with the exact sum of remainder labels. -/
inductive Steps {w : ℕ} : State w → ℕ → State w → Prop
  | refl (s) : Steps s 0 s
  | cons {s t u k l} : Step s k t → Steps t l u → Steps s (k+l) u

lemma Steps.single {w k} {s t : State w} (h : Step s k t) : Steps s k t := by
  simpa using Steps.cons h (Steps.refl t)

lemma Steps.trans {w k l} {s t u : State w} (h : Steps s k t) (h' : Steps t l u) :
    Steps s (k+l) u := by
  induction h with
  | refl => simpa using h'
  | cons hs ht ih => simpa [Nat.add_assoc] using Steps.cons hs (ih h')

def State.context {w} (s : State w) (cs : List (Instr w)) (vs : List Value) : State w :=
  ⟨s.control ++ cs, s.values ++ vs⟩

/-- Transition locality: a transition stays a transition, with the same cost, when control and
value stacks are appended below it. -/
lemma Step.context {w k} {s t : State w} (h : Step s k t) (cs vs) :
    Step (s.context cs vs) k (t.context cs vs) := by
  cases h with
  | var r i cs' vs' => simpa [State.context] using Step.var r i (cs'++cs) (vs'++vs)
  | compRem r a b cs' vs' =>
    simpa [State.context] using Step.compRem r a b (cs'++cs) (vs'++vs)
  | compZero r a b c cs' vs' =>
    simpa [State.context] using Step.compZero r a b c (cs'++cs) (vs'++vs)
  | compTest a cs' vs' => simpa [State.context] using Step.compTest a (cs'++cs) (vs'++vs)
  | compCall r f args cs' vs' =>
    simpa [State.context, List.append_assoc] using Step.compCall r f args (cs'++cs) (vs'++vs)
  | rem x y hp cs' vs' => simpa [State.context] using Step.rem x y hp (cs'++cs) (vs'++vs)
  | eq0 x cs' vs' => simpa [State.context] using Step.eq0 x (cs'++cs) (vs'++vs)
  | branchTrue a b cs' vs' =>
    simpa [State.context] using Step.branchTrue a b (cs'++cs) (vs'++vs)
  | branchFalse a b cs' vs' =>
    simpa [State.context] using Step.branchFalse a b (cs'++cs) (vs'++vs)
  | call f r body hb cs' vs' =>
    simpa [State.context, List.append_assoc] using Step.call f r body hb (cs'++cs) (vs'++vs)

lemma Steps.context {w k} {s t : State w} (h : Steps s k t) (cs vs) :
    Steps (s.context cs vs) k (t.context cs vs) := by
  induction h with
  | refl => exact .refl _
  | cons hs ht ih => exact .cons (hs.context cs vs) ih

lemma steps_arguments {w n k} {r : Registers n} {args : Fin k → Expr w n}
    {costs values : Fin k → ℕ}
    (h : ∀ i cs vs, Steps ⟨.eval (.mk r (args i)) :: cs, vs⟩ (costs i)
      ⟨cs, .nat (values i) :: vs⟩) (cs vs) :
    Steps ⟨arguments r args ++ cs, vs⟩ (∑ i, costs i)
      ⟨cs, List.ofFn (fun i => Value.nat (values i)) ++ vs⟩ := by
  induction k generalizing vs with
  | zero => simpa [arguments] using Steps.refl (⟨cs, vs⟩ : State w)
  | succ k ih =>
    have hlast := h (Fin.last k) (arguments r (fun i => args i.castSucc) ++ cs) vs
    have hrest := ih (args := fun i => args i.castSucc)
      (costs := fun i => costs i.castSucc) (values := fun i => values i.castSucc)
      (fun i => h i.castSucc) (.nat (values (Fin.last k)) :: vs)
    simpa only [arguments, List.cons_append, Fin.sum_univ_castSucc, List.ofFn_succ',
      List.concat_eq_append, List.append_assoc, List.singleton_append, List.nil_append,
      Nat.add_comm] using hlast.trans hrest

/-- Completeness, with arbitrary surrounding control and value stacks. -/
theorem eval_steps {w n K z} {r : Registers n} {e : Expr w n} (h : Eval r e K z)
    (cs vs) : Steps ⟨.eval (.mk r e) :: cs, vs⟩ K ⟨cs, .nat z :: vs⟩ := by
  induction h generalizing cs vs with
  | var r i => exact Steps.single (.var r i cs vs)
  | @rem n r a b K L x y ha hb hp iha ihb =>
    have ht := (ihb (.eval (.mk r a) :: .rem :: cs) vs).trans
      ((iha (.rem :: cs) (.nat y :: vs)).trans (Steps.single (.rem x y hp cs vs)))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Steps.cons (.compRem r a b cs vs) ht
  | @zero n r a b c K L z ha hb iha ihb =>
    have ht := (iha (.eq0 :: .branch (.mk r b) (.mk r c) :: cs) vs).trans
      ((Steps.single (.eq0 0 (.branch (.mk r b) (.mk r c) :: cs) vs)).trans
      ((Steps.single (.branchTrue (.mk r b) (.mk r c) cs vs)).trans (ihb cs vs)))
    simpa using Steps.cons (.compZero r a b c cs vs)
      (Steps.cons (.compTest (.mk r a) (.branch (.mk r b) (.mk r c) :: cs) vs) ht)
  | @pos n r a b c K L x z ha hp hc iha ihc =>
    have heq : decide (x=0) = false := by simp [show x ≠ 0 by omega]
    have ht := (iha (.eq0 :: .branch (.mk r b) (.mk r c) :: cs) vs).trans
      ((Steps.single (.eq0 x (.branch (.mk r b) (.mk r c) :: cs) vs)).trans
      (heq ▸ ((Steps.single (.branchFalse (.mk r b) (.mk r c) cs vs)).trans (ihc cs vs))))
    simpa using Steps.cons (.compZero r a b c cs vs)
      (Steps.cons (.compTest (.mk r a) (.branch (.mk r b) (.mk r c) :: cs) vs) ht)
  | @call n r f args costs values body K z ha hb hc iha ihc =>
    have ht := (steps_arguments iha (.call f :: cs) vs).trans
      ((Steps.single (.call f values body hb cs vs)).trans (ihc cs vs))
    simpa using Steps.cons (.compCall r f args cs vs) ht

/-- A continuation interpretation used only to prove soundness. Evaluating a
source term uses `Eval`; the other constructors interpret pending stack work. -/
inductive Finishes {w : ℕ} : State w → ℕ → ℕ → Prop
  | done (z) : Finishes ⟨[], [.nat z]⟩ 0 z
  | eval {n} {r : Registers n} {e : Expr w n} {K L x z cs vs} :
      Eval r e K x → Finishes ⟨cs, .nat x :: vs⟩ L z →
      Finishes ⟨.eval (.mk r e) :: cs, vs⟩ (K+L) z
  | rem {x y K z cs vs} : 0 < y → Finishes ⟨cs, .nat (x%y) :: vs⟩ K z →
      Finishes ⟨.rem :: cs, .nat x :: .nat y :: vs⟩ (1+K) z
  | eq0 {x K z cs vs} : Finishes ⟨cs, .bool (decide (x=0)) :: vs⟩ K z →
      Finishes ⟨.eq0 :: cs, .nat x :: vs⟩ K z
  | test {a K z cs vs} : Finishes ⟨.eval a :: .eq0 :: cs, vs⟩ K z →
      Finishes ⟨.test a :: cs, vs⟩ K z
  | branchTrue {a b K z cs vs} : Finishes ⟨.eval a :: cs, vs⟩ K z →
      Finishes ⟨.branch a b :: cs, .bool true :: vs⟩ K z
  | branchFalse {a b K z cs vs} : Finishes ⟨.eval b :: cs, vs⟩ K z →
      Finishes ⟨.branch a b :: cs, .bool false :: vs⟩ K z
  | call {f} {r : Registers (f.arity w)} {body : Expr w (f.arity w)}
      {K z cs vs} : body ∈ bodies w f → Finishes ⟨.eval (.mk r body) :: cs, vs⟩ K z →
      Finishes ⟨.call f :: cs, List.ofFn (fun i => Value.nat (r i)) ++ vs⟩ K z

lemma Finishes.eval_inv {w n K z cs vs} {r : Registers n} {e : Expr w n}
    (h : Finishes ⟨.eval (.mk r e) :: cs, vs⟩ K z) :
    ∃ k l x, Eval r e k x ∧ Finishes ⟨cs, .nat x :: vs⟩ l z ∧ K = k+l := by
  cases h with
  | eval he ht => exact ⟨_, _, _, he, ht, rfl⟩

lemma finishes_arguments {w n k K z cs vs} {r : Registers n} {args : Fin k → Expr w n}
    (h : Finishes ⟨arguments r args ++ cs, vs⟩ K z) :
    ∃ (costs values : Fin k → ℕ), ∃ L, (∀ i, Eval r (args i) (costs i) (values i)) ∧
      Finishes ⟨cs, List.ofFn (fun i => Value.nat (values i)) ++ vs⟩ L z ∧
      K = (∑ i, costs i)+L := by
  induction k generalizing K vs with
  | zero => exact ⟨Fin.elim0, Fin.elim0, K, fun i => i.elim0, by simpa [arguments] using h, by simp⟩
  | succ k ih =>
    simp only [arguments, List.cons_append] at h
    obtain ⟨a, b, x, he, ht, hK⟩ := h.eval_inv
    obtain ⟨costs, values, L, ha, htail, hB⟩ := ih ht
    refine ⟨Fin.snoc costs a, Fin.snoc values x, L, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using he
      · simpa using ha j
    · simpa only [List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last,
        List.concat_eq_append, List.append_assoc, List.singleton_append, List.nil_append] using htail
    · simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      omega

lemma values_append_inj {k : ℕ} {r s : Fin k → ℕ} {vs ws : List Value}
    (h : List.ofFn (fun i => Value.nat (r i)) ++ vs =
      List.ofFn (fun i => Value.nat (s i)) ++ ws) : r = s ∧ vs = ws := by
  have hlen : (List.ofFn (fun i => Value.nat (r i))).length =
      (List.ofFn (fun i => Value.nat (s i))).length := by simp
  have hp := List.append_inj h hlen
  refine ⟨?_, hp.2⟩
  have hf := List.ofFn_injective hp.1
  funext i
  exact Value.nat.inj (congrFun hf i)

lemma Finishes.call_inv {w f K z cs vs} {r : Registers (f.arity w)}
    (h : Finishes ⟨.call f :: cs, List.ofFn (fun i => Value.nat (r i)) ++ vs⟩ K z) :
    ∃ body, body ∈ bodies w f ∧ Finishes ⟨.eval (.mk r body) :: cs, vs⟩ K z := by
  generalize hv : List.ofFn (fun i => Value.nat (r i)) ++ vs = stack at h
  cases h with
  | call hb ht =>
    obtain ⟨hr, hs⟩ := values_append_inj hv
    subst_vars
    exact ⟨_, hb, ht⟩

lemma Step.finishes {w k l z} {s t : State w} (hs : Step s k t)
    (ht : Finishes t l z) : Finishes s (k+l) z := by
  cases hs with
  | var r i cs vs => exact .eval (.var r i) ht
  | compRem r a b cs vs =>
    obtain ⟨kb, lb, y, hb, ht, hL⟩ := ht.eval_inv
    obtain ⟨ka, la, x, ha, ht, hLb⟩ := ht.eval_inv
    cases ht with
    | rem hp ht =>
      have h := Finishes.eval (Eval.rem ha hb hp) ht
      convert h using 1; omega
  | compZero r a b c cs vs =>
    cases ht with
    | test ht =>
      obtain ⟨ka, la, x, ha, ht, hL⟩ := ht.eval_inv
      cases ht with
      | eq0 ht =>
        by_cases hx : x = 0
        · subst x
          simp only [decide_true] at ht
          cases ht with
          | branchTrue ht =>
            obtain ⟨kb, lb, y, hb, ht, hLa⟩ := ht.eval_inv
            have h := Finishes.eval (Eval.zero (c := c) ha hb) ht
            convert h using 1; omega
        · simp only [hx, decide_false] at ht
          cases ht with
          | branchFalse ht =>
            obtain ⟨kc, lc, y, hc, ht, hLa⟩ := ht.eval_inv
            have h := Finishes.eval (Eval.pos (b := b) ha (by omega) hc) ht
            convert h using 1; omega
  | compTest a cs vs => simpa using Finishes.test ht
  | compCall r f args cs vs =>
    obtain ⟨costs, values, L, ha, ht, hL⟩ := finishes_arguments ht
    obtain ⟨body, hb, ht⟩ := ht.call_inv
    obtain ⟨kb, lb, x, he, ht, hLb⟩ := ht.eval_inv
    have h := Finishes.eval (Eval.call ha hb he) ht
    convert h using 1; omega
  | rem x y hp cs vs => exact .rem hp ht
  | eq0 x cs vs => simpa using Finishes.eq0 ht
  | branchTrue a b cs vs => simpa using Finishes.branchTrue ht
  | branchFalse a b cs vs => simpa using Finishes.branchFalse ht
  | call f r body hb cs vs => simpa using Finishes.call hb ht

lemma Steps.finishes {w k l z} {s t : State w} (hs : Steps s k t)
    (ht : Finishes t l z) : Finishes s (k+l) z := by
  induction hs with
  | refl => simpa using ht
  | cons hs hrest ih => simpa [Nat.add_assoc] using hs.finishes (ih ht)

/-- `Eval r e K z` holds iff the machine runs from evaluating `e` under `r` to the value `z`
with total remainder cost `K`, for every term `e`. -/
theorem eval_iff_steps {w n K z} {r : Registers n} {e : Expr w n} :
    Eval r e K z ↔ Steps ⟨[.eval (.mk r e)], []⟩ K ⟨[], [.nat z]⟩ := by
  constructor
  · intro h
    exact eval_steps h [] []
  · intro h
    have hf : Finishes ⟨[.eval (.mk r e)], []⟩ K z := by
      simpa using h.finishes (Finishes.done z)
    obtain ⟨k, l, x, he, ht, hK⟩ := hf.eval_inv
    cases ht
    simpa [hK] using he

def start (w a b : ℕ) : State w := ⟨[.eval (.mk ![a,b] (head w))], []⟩
def halt (w z : ℕ) : State w := ⟨[], [.nat z]⟩

/-- Every halting machine computation from `start w a b` outputs `gcd(a, b)`. -/
theorem head_correct {w a b K z} (h : Steps (start w a b) K (halt w z)) :
    z = Nat.gcd a b := eval_head_correct (eval_iff_steps.mpr h)

/-- For `w ≥ 2`, the machine has a halting computation from `start w a b` with output
`gcd(a, b)`. -/
theorem head_exists {w} (hw : 2 ≤ w) (a b : ℕ) :
    ∃ K, Steps (start w a b) K (halt w (Nat.gcd a b)) := by
  obtain ⟨K, hK⟩ := eval_head_exists hw a b
  exact ⟨K, eval_iff_steps.mp hK⟩

/-- For `p > 0` and `C > 3/p`: for all sufficiently large `a` and every `b ≤ a`, the machine for
width `4^p + 5` halts from `start` with output `gcd(a, b)` at remainder cost at most
`C log₂ a`. -/
theorem eventually_steps_bound {p : ℕ} (hp : 0 < p) {C : ℝ} (hC : 3/(p:ℝ) < C) :
    ∀ᶠ a : ℕ in Filter.atTop, ∀ b, b ≤ a → ∃ K,
      Steps (start (Fixed.width p) a b) K (halt (Fixed.width p) (Nat.gcd a b)) ∧
        (K:ℝ) ≤ C*Real.logb 2 a := by
  filter_upwards [eventually_eval_bound hp hC] with a ha
  intro b hb
  obtain ⟨K, he, hK⟩ := ha b hb
  exact ⟨K, eval_iff_steps.mp he, hK⟩

/-- **Fixed programs with arbitrarily small coefficients**, for the machine: for every `ε > 0`
there are `p > 0` and `B ≥ 0` such that, for all `1 ≤ b ≤ a`, the machine for width `4^p + 5`
halts from `start` with output `gcd(a, b)` at remainder cost at most `ε log₂ a + B`. -/
theorem arbitrarily_small_program {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℕ, 0 < p ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℕ, 1 ≤ b → b ≤ a →
      ∃ K, Steps (start (Fixed.width p) a b) K (halt (Fixed.width p) (Nat.gcd a b)) ∧
        (K:ℝ) ≤ ε*Real.logb 2 a+B := by
  obtain ⟨p, hp, B, hB, h⟩ := Syntax.arbitrarily_small_program hε
  refine ⟨p, hp, B, hB, ?_⟩
  intro a b hb hab
  obtain ⟨K, he, hK⟩ := h a b hb hab
  exact ⟨K, eval_iff_steps.mp he, hK⟩

end ShortGCD.RegisterProgram.Syntax.Machine
