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

end Machine

end ShortGCD.Recursive
