module

public import Mathlib

@[expose] public section

/-! # Finite nondeterministic recursive programs and the two-stack machine

A program is given by a type `F` of internal function symbols, their arities `ar`, and for
each symbol a set `B f` of bodies; several bodies make the program nondeterministic, as in
Moschovakis, *Abstract Recursion and Intrinsic Complexity* (2019), §2E. Terms have
variables, remainder, the zero test `iteZero a b c` (`b` if `a = 0`, else `c`) and calls of
internal symbols. There are no numeric literals. `Eval` is call-by-value evaluation, counting
remainder calls; internal calls and zero tests are uncharged.

`Machine` is a specialisation of the book's recursive machine (Table 1, p. 75). The control
stack is stored with its top at the head (the reverse of the book's printed left stack),
argument terms are pushed right to left, `eq0` and the following branch are separate
transitions, and only remainder transitions have cost one. Closures represent substitution of
values into source terms, not data available to the program. `Machine.eval_iff_steps` proves
exact-cost equivalence with `Eval`, for every program and term.
-/

namespace ShortGCD.Recursive

variable {F : Type} {ar : F → ℕ}

/-- Terms over `n` variables. -/
inductive Expr (ar : F → ℕ) (n : ℕ) where
  | var : Fin n → Expr ar n
  | rem : Expr ar n → Expr ar n → Expr ar n
  | iteZero : Expr ar n → Expr ar n → Expr ar n → Expr ar n
  | app (f : F) : (Fin (ar f) → Expr ar n) → Expr ar n

/-- An expression containing no calls of internal functions. Primitive operations
and zero-test conditionals are allowed. -/
def Expr.CallFree {n} : Expr ar n → Prop
  | .var _ => True
  | .rem a b => a.CallFree ∧ b.CallFree
  | .iteZero a b c => a.CallFree ∧ b.CallFree ∧ c.CallFree
  | .app _ _ => False

/-- Every internal call occurs in tail position. Call arguments, remainder operands
and conditional guards must be call-free; conditional branches inherit tail position. -/
def Expr.TailCalls {n} : Expr ar n → Prop
  | .var _ => True
  | .rem a b => a.CallFree ∧ b.CallFree
  | .iteZero a b c => a.CallFree ∧ b.TailCalls ∧ c.TailCalls
  | .app _ args => ∀ i, (args i).CallFree

/-- The head and every alternative body have only tail-position internal calls. -/
def IsTailRecursive {n} (B : (f : F) → Set (Expr ar (ar f))) (head : Expr ar n) : Prop :=
  head.TailCalls ∧ ∀ f body, body ∈ B f → body.TailCalls

/-- The number of constructors in a term. -/
def Expr.size {n} : Expr ar n → ℕ
  | .var _ => 1
  | .rem a b => 1 + a.size + b.size
  | .iteZero a b c => 1 + a.size + b.size + c.size
  | .app _ args => 1 + ∑ i, (args i).size

lemma Expr.size_pos {n} (e : Expr ar n) : 1 ≤ e.size := by
  cases e <;> simp [Expr.size] <;> omega

/-- Call-by-value evaluation with bodies `B`. All arguments are evaluated before a body is
entered, and the cost is the number of remainder calls. -/
inductive Eval (B : (f : F) → Set (Expr ar (ar f))) :
    {n : ℕ} → (Fin n → ℕ) → Expr ar n → ℕ → ℕ → Prop
  | var {n} (r : Fin n → ℕ) (i : Fin n) : Eval B r (.var i) 0 (r i)
  | rem {n} {r : Fin n → ℕ} {a b : Expr ar n} {K L x y}
      (ha : Eval B r a K x) (hb : Eval B r b L y) (hp : 0 < y) :
      Eval B r (.rem a b) (K+L+1) (x%y)
  | zero {n} {r : Fin n → ℕ} {a b c : Expr ar n} {K L z}
      (ha : Eval B r a K 0) (hb : Eval B r b L z) : Eval B r (.iteZero a b c) (K+L) z
  | pos {n} {r : Fin n → ℕ} {a b c : Expr ar n} {K L x z}
      (ha : Eval B r a K x) (hp : 0 < x) (hc : Eval B r c L z) :
      Eval B r (.iteZero a b c) (K+L) z
  | call {n} {r : Fin n → ℕ} {f : F} {args : Fin (ar f) → Expr ar n}
      {costs values : Fin (ar f) → ℕ} {body : Expr ar (ar f)} {K z}
      (ha : ∀ i, Eval B r (args i) (costs i) (values i))
      (hb : body ∈ B f) (hc : Eval B values body K z) :
      Eval B r (.app f args) ((∑ i, costs i)+K) z

variable {B : (f : F) → Set (Expr ar (ar f))}

/-- Common divisors of the variables divide the value of every convergent evaluation. -/
theorem Eval.dvd {n K z d} {r : Fin n → ℕ} {e : Expr ar n} (h : Eval B r e K z)
    (hd : ∀ i, d ∣ r i) : d ∣ z := by
  induction h with
  | var r i => exact hd i
  | rem ha hb hp iha ihb => exact (Nat.dvd_mod_iff (ihb hd)).mpr (iha hd)
  | zero ha hb iha ihb => exact ihb hd
  | pos ha hp hc iha ihc => exact ihc hd
  | call ha hb hc iha ihc => exact ihc (fun i => iha i hd)

lemma Eval.var_spec {n K z} {r : Fin n → ℕ} {i : Fin n}
    (h : Eval B r (.var i) K z) : K = 0 ∧ z = r i := by
  cases h
  exact ⟨rfl, rfl⟩

lemma Eval.rem_vars_spec {n K z} {r : Fin n → ℕ} {i j : Fin n}
    (h : Eval B r (.rem (.var i) (.var j)) K z) :
    K = 1 ∧ z = r i % r j ∧ 0 < r j := by
  cases h with
  | rem ha hb hp =>
    cases ha
    cases hb
    exact ⟨rfl, rfl, hp⟩

namespace Machine

inductive Closure (ar : F → ℕ) where
  | mk {n : ℕ} (r : Fin n → ℕ) (e : Expr ar n)

inductive Value where
  | nat : ℕ → Value
  | bool : Bool → Value
  deriving DecidableEq

inductive Instr (ar : F → ℕ) where
  | eval : Closure ar → Instr ar
  | test : Closure ar → Instr ar
  | rem : Instr ar
  | eq0 : Instr ar
  | branch : Closure ar → Closure ar → Instr ar
  | call : F → Instr ar

def arguments {n : ℕ} (r : Fin n → ℕ) :
    {k : ℕ} → (Fin k → Expr ar n) → List (Instr ar)
  | 0, _ => []
  | k+1, args => .eval (.mk r (args (Fin.last k))) ::
      arguments r (fun i => args i.castSucc)

structure State (ar : F → ℕ) where
  control : List (Instr ar)
  values : List Value

/-- The transition table: pass, composition, external and internal calls, and branching.
The only nondeterminism is the choice of body at an internal call. -/
inductive Step (B : (f : F) → Set (Expr ar (ar f))) : State ar → ℕ → State ar → Prop
  | var {n} (r : Fin n → ℕ) (i : Fin n) (cs vs) :
      Step B ⟨.eval (.mk r (.var i)) :: cs, vs⟩ 0 ⟨cs, .nat (r i) :: vs⟩
  | compRem {n} (r : Fin n → ℕ) (a b : Expr ar n) (cs vs) :
      Step B ⟨.eval (.mk r (.rem a b)) :: cs, vs⟩ 0
        ⟨.eval (.mk r b) :: .eval (.mk r a) :: .rem :: cs, vs⟩
  | compZero {n} (r : Fin n → ℕ) (a b c : Expr ar n) (cs vs) :
      Step B ⟨.eval (.mk r (.iteZero a b c)) :: cs, vs⟩ 0
        ⟨.test (.mk r a) :: .branch (.mk r b) (.mk r c) :: cs, vs⟩
  | compTest (a : Closure ar) (cs vs) :
      Step B ⟨.test a :: cs, vs⟩ 0 ⟨.eval a :: .eq0 :: cs, vs⟩
  | compCall {n} (r : Fin n → ℕ) (f : F) (args : Fin (ar f) → Expr ar n) (cs vs) :
      Step B ⟨.eval (.mk r (.app f args)) :: cs, vs⟩ 0
        ⟨arguments r args ++ .call f :: cs, vs⟩
  | rem (x y : ℕ) (hp : 0 < y) (cs vs) :
      Step B ⟨.rem :: cs, .nat x :: .nat y :: vs⟩ 1 ⟨cs, .nat (x%y) :: vs⟩
  | eq0 (x : ℕ) (cs vs) :
      Step B ⟨.eq0 :: cs, .nat x :: vs⟩ 0 ⟨cs, .bool (decide (x=0)) :: vs⟩
  | branchTrue (a b : Closure ar) (cs vs) :
      Step B ⟨.branch a b :: cs, .bool true :: vs⟩ 0 ⟨.eval a :: cs, vs⟩
  | branchFalse (a b : Closure ar) (cs vs) :
      Step B ⟨.branch a b :: cs, .bool false :: vs⟩ 0 ⟨.eval b :: cs, vs⟩
  | call (f : F) (r : Fin (ar f) → ℕ) (body : Expr ar (ar f))
      (hb : body ∈ B f) (cs vs) :
      Step B ⟨.call f :: cs, List.ofFn (fun i => Value.nat (r i)) ++ vs⟩ 0
        ⟨.eval (.mk r body) :: cs, vs⟩

/-- Finite transition sequences with the exact sum of remainder labels. -/
inductive Steps (B : (f : F) → Set (Expr ar (ar f))) : State ar → ℕ → State ar → Prop
  | refl (s) : Steps B s 0 s
  | cons {s t u k l} : Step B s k t → Steps B t l u → Steps B s (k+l) u

lemma Steps.single {k} {s t : State ar} (h : Step B s k t) : Steps B s k t := by
  simpa using Steps.cons h (Steps.refl t)

lemma Steps.trans {k l} {s t u : State ar} (h : Steps B s k t) (h' : Steps B t l u) :
    Steps B s (k+l) u := by
  induction h with
  | refl => simpa using h'
  | cons hs ht ih => simpa [Nat.add_assoc] using Steps.cons hs (ih h')

def State.context (s : State ar) (cs : List (Instr ar)) (vs : List Value) : State ar :=
  ⟨s.control ++ cs, s.values ++ vs⟩

/-- Transition locality: a transition stays a transition, with the same cost, when control and
value stacks are appended below it. -/
lemma Step.context {k} {s t : State ar} (h : Step B s k t) (cs vs) :
    Step B (s.context cs vs) k (t.context cs vs) := by
  cases h with
  | var r i cs' vs' => simpa [State.context] using Step.var (B := B) r i (cs'++cs) (vs'++vs)
  | compRem r a b cs' vs' =>
    simpa [State.context] using Step.compRem (B := B) r a b (cs'++cs) (vs'++vs)
  | compZero r a b c cs' vs' =>
    simpa [State.context] using Step.compZero (B := B) r a b c (cs'++cs) (vs'++vs)
  | compTest a cs' vs' =>
    simpa [State.context] using Step.compTest (B := B) a (cs'++cs) (vs'++vs)
  | compCall r f args cs' vs' =>
    simpa [State.context, List.append_assoc] using
      Step.compCall (B := B) r f args (cs'++cs) (vs'++vs)
  | rem x y hp cs' vs' => simpa [State.context] using Step.rem (B := B) x y hp (cs'++cs) (vs'++vs)
  | eq0 x cs' vs' => simpa [State.context] using Step.eq0 (B := B) x (cs'++cs) (vs'++vs)
  | branchTrue a b cs' vs' =>
    simpa [State.context] using Step.branchTrue (B := B) a b (cs'++cs) (vs'++vs)
  | branchFalse a b cs' vs' =>
    simpa [State.context] using Step.branchFalse (B := B) a b (cs'++cs) (vs'++vs)
  | call f r body hb cs' vs' =>
    simpa [State.context, List.append_assoc] using Step.call f r body hb (cs'++cs) (vs'++vs)

lemma Steps.context {k} {s t : State ar} (h : Steps B s k t) (cs vs) :
    Steps B (s.context cs vs) k (t.context cs vs) := by
  induction h with
  | refl => exact .refl _
  | cons hs ht ih => exact .cons (hs.context cs vs) ih

lemma steps_arguments {n k} {r : Fin n → ℕ} {args : Fin k → Expr ar n}
    {costs values : Fin k → ℕ}
    (h : ∀ i cs vs, Steps B ⟨.eval (.mk r (args i)) :: cs, vs⟩ (costs i)
      ⟨cs, .nat (values i) :: vs⟩) (cs vs) :
    Steps B ⟨arguments r args ++ cs, vs⟩ (∑ i, costs i)
      ⟨cs, List.ofFn (fun i => Value.nat (values i)) ++ vs⟩ := by
  induction k generalizing vs with
  | zero => simpa [arguments] using Steps.refl (B := B) (⟨cs, vs⟩ : State ar)
  | succ k ih =>
    have hlast := h (Fin.last k) (arguments r (fun i => args i.castSucc) ++ cs) vs
    have hrest := ih (args := fun i => args i.castSucc)
      (costs := fun i => costs i.castSucc) (values := fun i => values i.castSucc)
      (fun i => h i.castSucc) (.nat (values (Fin.last k)) :: vs)
    simpa only [arguments, List.cons_append, Fin.sum_univ_castSucc, List.ofFn_succ',
      List.concat_eq_append, List.append_assoc, List.singleton_append, List.nil_append,
      Nat.add_comm] using hlast.trans hrest

/-- Completeness, with arbitrary surrounding control and value stacks. -/
theorem eval_steps {n K z} {r : Fin n → ℕ} {e : Expr ar n} (h : Eval B r e K z)
    (cs vs) : Steps B ⟨.eval (.mk r e) :: cs, vs⟩ K ⟨cs, .nat z :: vs⟩ := by
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

/-- A continuation interpretation used only to prove soundness. Evaluating a source term uses
`Eval`; the other constructors interpret pending stack work. -/
inductive Finishes (B : (f : F) → Set (Expr ar (ar f))) : State ar → ℕ → ℕ → Prop
  | done (z) : Finishes B ⟨[], [.nat z]⟩ 0 z
  | eval {n} {r : Fin n → ℕ} {e : Expr ar n} {K L x z cs vs} :
      Eval B r e K x → Finishes B ⟨cs, .nat x :: vs⟩ L z →
      Finishes B ⟨.eval (.mk r e) :: cs, vs⟩ (K+L) z
  | rem {x y K z cs vs} : 0 < y → Finishes B ⟨cs, .nat (x%y) :: vs⟩ K z →
      Finishes B ⟨.rem :: cs, .nat x :: .nat y :: vs⟩ (1+K) z
  | eq0 {x K z cs vs} : Finishes B ⟨cs, .bool (decide (x=0)) :: vs⟩ K z →
      Finishes B ⟨.eq0 :: cs, .nat x :: vs⟩ K z
  | test {a K z cs vs} : Finishes B ⟨.eval a :: .eq0 :: cs, vs⟩ K z →
      Finishes B ⟨.test a :: cs, vs⟩ K z
  | branchTrue {a b K z cs vs} : Finishes B ⟨.eval a :: cs, vs⟩ K z →
      Finishes B ⟨.branch a b :: cs, .bool true :: vs⟩ K z
  | branchFalse {a b K z cs vs} : Finishes B ⟨.eval b :: cs, vs⟩ K z →
      Finishes B ⟨.branch a b :: cs, .bool false :: vs⟩ K z
  | call {f} {r : Fin (ar f) → ℕ} {body : Expr ar (ar f)}
      {K z cs vs} : body ∈ B f → Finishes B ⟨.eval (.mk r body) :: cs, vs⟩ K z →
      Finishes B ⟨.call f :: cs, List.ofFn (fun i => Value.nat (r i)) ++ vs⟩ K z

lemma Finishes.eval_inv {n K z cs vs} {r : Fin n → ℕ} {e : Expr ar n}
    (h : Finishes B ⟨.eval (.mk r e) :: cs, vs⟩ K z) :
    ∃ k l x, Eval B r e k x ∧ Finishes B ⟨cs, .nat x :: vs⟩ l z ∧ K = k+l := by
  cases h with
  | eval he ht => exact ⟨_, _, _, he, ht, rfl⟩

lemma finishes_arguments {n k K z cs vs} {r : Fin n → ℕ} {args : Fin k → Expr ar n}
    (h : Finishes B ⟨arguments r args ++ cs, vs⟩ K z) :
    ∃ (costs values : Fin k → ℕ), ∃ L, (∀ i, Eval B r (args i) (costs i) (values i)) ∧
      Finishes B ⟨cs, List.ofFn (fun i => Value.nat (values i)) ++ vs⟩ L z ∧
      K = (∑ i, costs i)+L := by
  induction k generalizing K vs with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, K, fun i => i.elim0, by simpa [arguments] using h, by simp⟩
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

lemma Finishes.call_inv {f K z cs vs} {r : Fin (ar f) → ℕ}
    (h : Finishes B ⟨.call f :: cs, List.ofFn (fun i => Value.nat (r i)) ++ vs⟩ K z) :
    ∃ body, body ∈ B f ∧ Finishes B ⟨.eval (.mk r body) :: cs, vs⟩ K z := by
  generalize hv : List.ofFn (fun i => Value.nat (r i)) ++ vs = stack at h
  cases h with
  | call hb ht =>
    obtain ⟨hr, hs⟩ := values_append_inj hv
    subst_vars
    exact ⟨_, hb, ht⟩

lemma Step.finishes {k l z} {s t : State ar} (hs : Step B s k t)
    (ht : Finishes B t l z) : Finishes B s (k+l) z := by
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

lemma Steps.finishes {k l z} {s t : State ar} (hs : Steps B s k t)
    (ht : Finishes B t l z) : Finishes B s (k+l) z := by
  induction hs with
  | refl => simpa using ht
  | cons hs hrest ih => simpa [Nat.add_assoc] using hs.finishes (ih ht)

/-- `Eval B r e K z` holds iff the machine runs from evaluating `e` under `r` to the value `z`
with total remainder cost `K`, for every program and term. -/
theorem eval_iff_steps {n K z} {r : Fin n → ℕ} {e : Expr ar n} :
    Eval B r e K z ↔ Steps B ⟨[.eval (.mk r e)], []⟩ K ⟨[], [.nat z]⟩ := by
  constructor
  · intro h
    exact eval_steps h [] []
  · intro h
    have hf : Finishes B ⟨[.eval (.mk r e)], []⟩ K z := by
      simpa using h.finishes (Finishes.done z)
    obtain ⟨k, l, x, he, ht, hK⟩ := hf.eval_inv
    cases ht
    simpa [hK] using he


/-! ## Bounded stacks for tail-recursive programs

For a tail-recursive program, the control and value stacks stay bounded by the largest
head or body, however long the computation runs. The proof keeps three invariants:
the control stack is call-free work followed by at most one tail instruction (`TailShape`);
the values plus the net number of values pending on the control stack total one
(`Instr.net`); and a size potential (`State.potential`) never increases except at a call,
where the first two invariants force both stacks to be empty below the call. -/

/-- A size weight for pending work. -/
def Instr.wt : Instr ar → ℕ
  | .eval (.mk _ e) => e.size
  | .test (.mk _ a) => a.size + 1
  | .rem => 1
  | .eq0 => 1
  | .branch (.mk _ b) (.mk _ c) => b.size + c.size
  | .call _ => 1

/-- The net number of values an instruction leaves on the value stack when it finishes. -/
def Instr.net : Instr ar → ℤ
  | .eval _ => 1
  | .test _ => 1
  | .rem => -1
  | .eq0 => 0
  | .branch _ _ => 0
  | .call f => 1 - (ar f : ℤ)

/-- Instructions whose remaining work makes no internal call. -/
def Instr.CF : Instr ar → Prop
  | .eval (.mk _ e) => e.CallFree
  | .test (.mk _ a) => a.CallFree
  | .rem => True
  | .eq0 => True
  | .branch (.mk _ b) (.mk _ c) => b.CallFree ∧ c.CallFree
  | .call _ => False

/-- Instructions allowed in tail position. -/
def Instr.Tail : Instr ar → Prop
  | .eval (.mk _ e) => e.TailCalls
  | .branch (.mk _ b) (.mk _ c) => b.TailCalls ∧ c.TailCalls
  | .call _ => True
  | _ => False

/-- Call-free work followed by at most one tail instruction. -/
def TailShape (cs : List (Instr ar)) : Prop :=
  ∃ pre tl, cs = pre ++ tl ∧ (∀ x ∈ pre, Instr.CF x) ∧ (tl = [] ∨ ∃ x, tl = [x] ∧ Instr.Tail x)

def State.potential (s : State ar) : ℕ := (s.control.map Instr.wt).sum + s.values.length

def State.net (s : State ar) : ℤ := (s.values.length : ℤ) + (s.control.map Instr.net).sum

lemma Instr.wt_pos (x : Instr ar) : 1 ≤ x.wt := by
  rcases x with ⟨r, e⟩ | ⟨r, a⟩ | _ | _ | ⟨⟨r, b⟩, ⟨r', c⟩⟩ | f <;>
    simp [Instr.wt, Expr.size_pos]
  have := b.size_pos; omega

lemma length_le_wt (cs : List (Instr ar)) : cs.length ≤ (cs.map Instr.wt).sum := by
  induction cs with
  | nil => simp
  | cons x cs ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; have := x.wt_pos; omega

lemma arguments_wt {n k} (r : Fin n → ℕ) (args : Fin k → Expr ar n) :
    ((arguments r args).map Instr.wt).sum = ∑ i, (args i).size := by
  induction k with
  | zero => simp [arguments]
  | succ k ih =>
    simp only [arguments, List.map_cons, List.sum_cons, Instr.wt, Fin.sum_univ_castSucc]
    rw [ih]; omega

lemma arguments_net {n k} (r : Fin n → ℕ) (args : Fin k → Expr ar n) :
    ((arguments r args).map Instr.net).sum = k := by
  induction k with
  | zero => simp [arguments]
  | succ k ih =>
    simp only [arguments, List.map_cons, List.sum_cons, Instr.net]
    rw [ih]; push_cast; ring

lemma arguments_CF {n k} (r : Fin n → ℕ) (args : Fin k → Expr ar n)
    (h : ∀ i, (args i).CallFree) : ∀ x ∈ arguments r args, Instr.CF x := by
  induction k with
  | zero => simp [arguments]
  | succ k ih =>
    intro x hx
    simp only [arguments, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h _
    · exact ih (fun i => args i.castSucc) (fun i => h _) x hx

/-- Every transition preserves the value accounting. -/
lemma Step.net_eq {k} {s t : State ar} (h : Step B s k t) : t.net = s.net := by
  cases h <;>
    simp [State.net, Instr.net, arguments_net, List.length_ofFn] <;> ring

/-- A call-free instruction at the top is replaced by call-free work. -/
lemma Step.cf_head {k} {s t : State ar} (h : Step B s k t) {x cs}
    (hs : s.control = x :: cs) (hx : Instr.CF x) :
    ∃ new, t.control = new ++ cs ∧ ∀ y ∈ new, Instr.CF y := by
  cases h with
  | var r i cs' vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    exact ⟨[], rfl, by simp⟩
  | compRem r a b cs' vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    obtain ⟨ha, hb⟩ := hx
    exact ⟨[.eval (.mk r b), .eval (.mk r a), .rem], rfl, by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro y (rfl | rfl | rfl) <;> simp [Instr.CF, ha, hb]⟩
  | compZero r a b c cs' vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    obtain ⟨ha, hb, hc⟩ := hx
    exact ⟨[.test (.mk r a), .branch (.mk r b) (.mk r c)], rfl, by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro y (rfl | rfl) <;> simp [Instr.CF, ha, hb, hc]⟩
  | compTest a cs' vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    obtain ⟨r, e⟩ := a
    exact ⟨[.eval (.mk r e), .eq0], rfl, by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro y (rfl | rfl) <;> simp_all [Instr.CF]⟩
  | compCall r f args cs' vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    exact hx.elim
  | rem x y hp cs' vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    exact ⟨[], rfl, by simp⟩
  | eq0 x cs' vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    exact ⟨[], rfl, by simp⟩
  | branchTrue a b cs' vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    obtain ⟨r, e⟩ := a
    obtain ⟨r', e'⟩ := b
    exact ⟨[.eval (.mk r e)], rfl, by simpa [Instr.CF] using hx.1⟩
  | branchFalse a b cs' vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    obtain ⟨r, e⟩ := a
    obtain ⟨r', e'⟩ := b
    exact ⟨[.eval (.mk r' e')], rfl, by simpa [Instr.CF] using hx.2⟩
  | call f r body hb cs' vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    exact hx.elim

/-- A lone tail instruction leaves a tail-shaped control stack. -/
lemma Step.tail_head {k} {s t : State ar} (h : Step B s k t) {x}
    (hs : s.control = [x]) (hx : Instr.Tail x)
    (hB : ∀ f body, body ∈ B f → body.TailCalls) : TailShape t.control := by
  cases h with
  | var r i cs vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    exact ⟨[], [], rfl, by simp, Or.inl rfl⟩
  | compRem r a b cs vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    obtain ⟨ha, hb⟩ := hx
    refine ⟨[.eval (.mk r b), .eval (.mk r a), .rem], [], by simp, ?_, Or.inl rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro y (rfl | rfl | rfl) <;> simp [Instr.CF, ha, hb]
  | compZero r a b c cs vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    obtain ⟨ha, hb, hc⟩ := hx
    refine ⟨[.test (.mk r a)], [.branch (.mk r b) (.mk r c)], rfl, ?_,
      Or.inr ⟨_, rfl, hb, hc⟩⟩
    simpa [Instr.CF] using ha
  | compTest a cs vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    exact hx.elim
  | compCall r f args cs vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    exact ⟨arguments r args, [.call f], rfl, arguments_CF r args hx,
      Or.inr ⟨_, rfl, trivial⟩⟩
  | rem x y hp cs vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    exact hx.elim
  | eq0 x cs vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    exact hx.elim
  | branchTrue a b cs vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    obtain ⟨r, e⟩ := a
    obtain ⟨r', e'⟩ := b
    exact ⟨[], [.eval (.mk r e)], rfl, by simp, Or.inr ⟨_, rfl, hx.1⟩⟩
  | branchFalse a b cs vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    obtain ⟨r, e⟩ := a
    obtain ⟨r', e'⟩ := b
    exact ⟨[], [.eval (.mk r' e')], rfl, by simp, Or.inr ⟨_, rfl, hx.2⟩⟩
  | call f r body hb cs vs =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hs
    exact ⟨[], [.eval (.mk r body)], rfl, by simp, Or.inr ⟨_, rfl, hB f body hb⟩⟩

lemma Step.control_ne_nil {k} {s t : State ar} (h : Step B s k t) : s.control ≠ [] := by
  cases h <;> simp

/-- Transitions preserve the tail shape. -/
lemma Step.tailShape {k} {s t : State ar} (h : Step B s k t)
    (hB : ∀ f body, body ∈ B f → body.TailCalls) (hs : TailShape s.control) :
    TailShape t.control := by
  obtain ⟨pre, tl, heq, hpre, htl⟩ := hs
  cases pre with
  | nil =>
    rcases htl with rfl | ⟨x, rfl, hx⟩
    · exact (h.control_ne_nil (by simpa using heq)).elim
    · exact h.tail_head (by simpa using heq) hx hB
  | cons y pre' =>
    obtain ⟨new, ht, hnew⟩ := h.cf_head (by simpa using heq) (hpre y (by simp))
    refine ⟨new ++ pre', tl, by simp [ht], ?_, htl⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hnew x hx
    · exact hpre x (by simp [hx])

/-- The three invariants, with potential bound `S`. -/
def Inv (S : ℕ) (s : State ar) : Prop := TailShape s.control ∧ s.net = 1 ∧ s.potential ≤ S

lemma Step.inv {S k} {s t : State ar} (h : Step B s k t)
    (hB : ∀ f body, body ∈ B f → body.TailCalls) (hBS : ∀ f body, body ∈ B f → body.size ≤ S)
    (hs : Inv S s) : Inv S t := by
  obtain ⟨hshape, hnet, hpot⟩ := hs
  refine ⟨h.tailShape hB hshape, by rw [h.net_eq, hnet], ?_⟩
  cases h with
  | var r i cs vs =>
    simp only [State.potential, List.map_cons, List.sum_cons, List.length_cons, Instr.wt,
      Expr.size] at hpot ⊢; omega
  | compRem r a b cs vs =>
    simp only [State.potential, List.map_cons, List.sum_cons, Instr.wt, Expr.size] at hpot ⊢
    omega
  | compZero r a b c cs vs =>
    simp only [State.potential, List.map_cons, List.sum_cons, Instr.wt, Expr.size] at hpot ⊢
    omega
  | compTest a cs vs =>
    obtain ⟨r, e⟩ := a
    simp only [State.potential, List.map_cons, List.sum_cons, Instr.wt] at hpot ⊢; omega
  | compCall r f args cs vs =>
    simp only [State.potential, List.map_cons, List.sum_cons, List.map_append, List.sum_append,
      Instr.wt, Expr.size, arguments_wt] at hpot ⊢; omega
  | rem x y hp cs vs =>
    simp only [State.potential, List.map_cons, List.sum_cons, List.length_cons, Instr.wt]
      at hpot ⊢; omega
  | eq0 x cs vs =>
    simp only [State.potential, List.map_cons, List.sum_cons, List.length_cons, Instr.wt]
      at hpot ⊢; omega
  | branchTrue a b cs vs =>
    obtain ⟨r, e⟩ := a
    obtain ⟨r', e'⟩ := b
    simp only [State.potential, List.map_cons, List.sum_cons, List.length_cons, Instr.wt]
      at hpot ⊢
    omega
  | branchFalse a b cs vs =>
    obtain ⟨r, e⟩ := a
    obtain ⟨r', e'⟩ := b
    simp only [State.potential, List.map_cons, List.sum_cons, List.length_cons, Instr.wt]
      at hpot ⊢
    omega
  | call f r body hb cs vs =>
    -- A pending call is the only instruction, and the value stack holds exactly its
    -- arguments, so the new potential is the size of the body.
    obtain ⟨pre, tl, heq, hpre, htl⟩ := hshape
    have hcs : cs = [] := by
      cases pre with
      | nil =>
        rcases htl with rfl | ⟨x, rfl, hx⟩
        · simp at heq
        · simpa using (List.cons.inj heq).2
      | cons y pre' =>
        have hy := hpre y (by simp)
        rw [(List.cons.inj heq).1.symm] at hy
        exact hy.elim
    subst hcs
    have hvs : vs = [] := by
      simp only [State.net, List.length_append, List.length_ofFn, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, Instr.net] at hnet
      push_cast at hnet
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hvs
    simpa [State.potential, Instr.wt] using hBS f body hb

lemma Steps.inv {S k} {s t : State ar} (h : Steps B s k t)
    (hB : ∀ f body, body ∈ B f → body.TailCalls) (hBS : ∀ f body, body ∈ B f → body.size ≤ S)
    (hs : Inv S s) : Inv S t := by
  induction h with
  | refl => exact hs
  | cons hstep _ ih => exact ih (hstep.inv hB hBS hs)

/-- **Bounded stacks.** For a tail-recursive program whose head and bodies have size at most
`S`, every state reachable from evaluating the head has control and value stacks of total
length at most `S`. The measure counts stack entries (instructions and values); closures in
control entries carry environments whose size is the arity of the term they belong to. No
termination is assumed: the bound holds along every finite prefix of every computation. -/
theorem stacks_bounded {n S k} {head : Expr ar n} {r : Fin n → ℕ} {t : State ar}
    (ht : IsTailRecursive B head) (hS : head.size ≤ S)
    (hBS : ∀ f body, body ∈ B f → body.size ≤ S)
    (h : Steps B ⟨[.eval (.mk r head)], []⟩ k t) :
    t.control.length + t.values.length ≤ S := by
  have h0 : Inv S (⟨[.eval (.mk r head)], []⟩ : State ar) := by
    refine ⟨⟨[], [.eval (.mk r head)], rfl, by simp, Or.inr ⟨_, rfl, ht.1⟩⟩, ?_, ?_⟩
    · simp [State.net, Instr.net]
    · simpa [State.potential, Instr.wt] using hS
  obtain ⟨-, -, hpot⟩ := h.inv ht.2 hBS h0
  have := length_le_wt t.control
  simp only [State.potential] at hpot
  omega

end Machine

end ShortGCD.Recursive
