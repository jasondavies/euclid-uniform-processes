import ShortGCD.ShapeCount

/-! # General recursive programs have few shapes

This file formalizes the Shape-Count Lemma of `research/shape-count.tex` for
general first-order recursive programs over `(ℕ, rem, eq₀, eq₁)`.

* **Syntax.** A program has a signature of function symbols with arities, a set
  of bodies for each symbol (several bodies give nondeterminism; the set need
  not be finite), and a main term in two input variables. Terms are built from
  variables, the truth values `tt` and `ff`, `rem`, the tests `eq₀` and `eq₁`,
  conditionals, and calls. There are no numeric constants.
* **Values.** Values are tagged `nat` or `bool`. Ill-sorted terms simply have no
  evaluation, so well-sorted two-sorted programs are the special case.
* **Semantics.** `Eval` is the big-step call-by-value evaluation relation. Every
  argument is evaluated before the chosen body. Conditionals evaluate only the
  chosen branch. The cost is the number of `rem` nodes. A convergent computation
  is a finite derivation of `Eval`.

**Main results.** Let every arity be at most `K`, with `2 ≤ K`.
* `eval_run`: every evaluation returning `1` compiles into a register run of
  width `2K+2` (`RegisterProgram.Run`) with the same number of remainder calls.
  Each subterm is evaluated in a subcomputation on a copy of the registers, so
  temporaries never overwrite the environment.
* `eval_shape`: every successful evaluation of cost at most `c` on an input
  `a, b ≥ 2` has a shape of length at most `c` in a fixed finite set
  `shapeSet (2K+2) c` that reaches `1` on `(a, b)`. `card_shapeSet_le_pow` shows
  this set has at most `(7·A⁵)^(c+1)` elements, where `A` depends only on `K`.
  This is the Shape-Count Lemma with `C_P = 7·A⁵`.
* `eval_shape_val`: provenance of the output. A computed value is a value of a
  valid shape.
* `card_eval_le` and `eventually_card_eval_le`: the counting consequences,
  mirroring `ShapeCount.card_run_le` and `eventually_card_run_le`.
* `double_or_one`, `decide_run` and `card_decide_le`: the same for programs that
  decide coprimeness with `eq₁`. A correct decision answering "coprime" on
  `a, b ≥ 2` yields a run returning `1` with no more remainder calls. Otherwise
  doubling every value would give a wrong convergent computation at `(2a, 2b)`.

The constant depends only on the maximal arity, not on the number or size of the
bodies.
-/

namespace ShortGCD.GeneralPrograms

open ShortGCD.RegisterProgram ShortGCD.ShapeCount

/-! ## Syntax and semantics -/

/-- Values of the two sorts. -/
inductive Val where
  | nat (x : ℕ)
  | bool (b : Bool)

/-- A signature: function symbols with arities. -/
structure Sig where
  F : Type
  arity : F → ℕ

/-- Terms with variables `Fin n`. -/
inductive Tm (σ : Sig) (n : ℕ) : Type where
  | var : Fin n → Tm σ n
  | tt : Tm σ n
  | ff : Tm σ n
  | rem : Tm σ n → Tm σ n → Tm σ n
  | eq0 : Tm σ n → Tm σ n
  | eq1 : Tm σ n → Tm σ n
  | ite : Tm σ n → Tm σ n → Tm σ n → Tm σ n
  | call (f : σ.F) : (Fin (σ.arity f) → Tm σ n) → Tm σ n

/-- A recursive program: equations `f(x₁, …, x_k) = body` for every body in
`bodies f`, and a main term in the two inputs. -/
structure Program where
  sig : Sig
  bodies : (f : sig.F) → Set (Tm sig (sig.arity f))
  main : Tm sig 2

/-- Big-step call-by-value evaluation with remainder cost. -/
inductive Eval (P : Program) : {n : ℕ} → (Fin n → Val) → Tm P.sig n → ℕ → Val → Prop
  | var {n} (ρ : Fin n → Val) (i : Fin n) : Eval P ρ (.var i) 0 (ρ i)
  | tt {n} (ρ : Fin n → Val) : Eval P ρ .tt 0 (.bool true)
  | ff {n} (ρ : Fin n → Val) : Eval P ρ .ff 0 (.bool false)
  | rem {n} {ρ : Fin n → Val} {s t : Tm P.sig n} {K L x y : ℕ}
      (hs : Eval P ρ s K (.nat x)) (ht : Eval P ρ t L (.nat y)) (hp : 0 < y) :
      Eval P ρ (.rem s t) (K + L + 1) (.nat (x % y))
  | eq0 {n} {ρ : Fin n → Val} {s : Tm P.sig n} {K x : ℕ}
      (hs : Eval P ρ s K (.nat x)) : Eval P ρ (.eq0 s) K (.bool (decide (x = 0)))
  | eq1 {n} {ρ : Fin n → Val} {s : Tm P.sig n} {K x : ℕ}
      (hs : Eval P ρ s K (.nat x)) : Eval P ρ (.eq1 s) K (.bool (decide (x = 1)))
  | iteT {n} {ρ : Fin n → Val} {c s t : Tm P.sig n} {K L : ℕ} {v : Val}
      (hc : Eval P ρ c K (.bool true)) (hs : Eval P ρ s L v) :
      Eval P ρ (.ite c s t) (K + L) v
  | iteF {n} {ρ : Fin n → Val} {c s t : Tm P.sig n} {K L : ℕ} {v : Val}
      (hc : Eval P ρ c K (.bool false)) (ht : Eval P ρ t L v) :
      Eval P ρ (.ite c s t) (K + L) v
  | call {n} {ρ : Fin n → Val} {f : P.sig.F} {args : Fin (P.sig.arity f) → Tm P.sig n}
      {costs : Fin (P.sig.arity f) → ℕ} {vals : Fin (P.sig.arity f) → Val}
      {body : Tm P.sig (P.sig.arity f)} {M : ℕ} {v : Val}
      (ha : ∀ i, Eval P ρ (args i) (costs i) (vals i)) (hb : body ∈ P.bodies f)
      (hc : Eval P vals body M v) :
      Eval P ρ (.call f args) ((∑ i, costs i) + M) v

/-! ## Compilation into register runs of width `2K+2` -/

/-- Registers `0, …, n-1` hold the natural-number entries of the environment.
Registers `K, …, 2K-1` collect call arguments. Registers `2K` and `2K+1` are
remainder temporaries. -/
def Agree (K : ℕ) {n : ℕ} (hn : n ≤ K) (r : Registers (2 * K + 2)) (ρ : Fin n → Val) :
    Prop :=
  ∀ (i : Fin n) (x : ℕ), ρ i = .nat x → r ⟨i, by have := i.isLt; omega⟩ = x

theorem Agree.update {K n : ℕ} {hn : n ≤ K} {r : Registers (2 * K + 2)} {ρ : Fin n → Val}
    (h : Agree K hn r ρ) (d : Fin (2 * K + 2)) (hd : K ≤ d.val) (y : ℕ) :
    Agree K hn (Function.update r d y) ρ := by
  intro i x hx
  have hne : (⟨i, by have := i.isLt; omega⟩ : Fin (2 * K + 2)) ≠ d := by
    intro he
    have := congrArg Fin.val he
    simp at this
    have := i.isLt
    omega
  rw [Function.update_of_ne hne]
  exact h i x hx

/-- Evaluating the arguments of a call one after another, each in its own
subcomputation, fills the argument registers and leaves the environment intact. -/
theorem args_run {K n : ℕ} (hn : n ≤ K) {ρ : Fin n → Val} :
    ∀ (k : ℕ) (hk : k ≤ K) (costs : Fin k → ℕ) (vals : Fin k → Val),
    (∀ (i : Fin k) (r : Registers (2 * K + 2)), Agree K hn r ρ →
      ∃ z, Run r (costs i) z ∧ ∀ x, vals i = .nat x → z = x) →
    ∀ r : Registers (2 * K + 2), Agree K hn r ρ →
      ∃ r' : Registers (2 * K + 2), Agree K hn r' ρ ∧
        (∀ (i : Fin k) (x : ℕ), vals i = .nat x →
          r' ⟨K + i, by have := i.isLt; omega⟩ = x) ∧
        ∀ m z, Run r' m z → Run r ((∑ i, costs i) + m) z := by
  intro k
  induction k with
  | zero =>
    intro _ costs vals _ r hr
    exact ⟨r, hr, fun i => i.elim0, fun m z h => by simpa using h⟩
  | succ k ih =>
    intro hk costs vals hev r hr
    obtain ⟨r₁, hr₁, hs₁, ht₁⟩ := ih (by omega) (costs ∘ Fin.castSucc) (vals ∘ Fin.castSucc)
      (fun i => hev i.castSucc) r hr
    obtain ⟨z, hz, hzv⟩ := hev (Fin.last k) r₁ hr₁
    set d : Fin (2 * K + 2) := ⟨K + k, by omega⟩ with hd
    refine ⟨Function.update r₁ d z, hr₁.update d (by simp [hd]) z, ?_, ?_⟩
    · intro i x hx
      refine Fin.lastCases ?_ (fun j hx => ?_) i hx
      · intro hx
        have : (⟨K + (Fin.last k : ℕ), by omega⟩ : Fin (2 * K + 2)) = d := by
          simp [hd]
        rw [this, Function.update_self]
        exact hzv x hx
      · have hne : (⟨K + (j.castSucc : ℕ), by have := j.isLt; omega⟩ : Fin (2 * K + 2)) ≠ d := by
          intro he
          have := congrArg Fin.val he
          simp [hd] at this
          have := j.isLt
          omega
        rw [Function.update_of_ne hne]
        simpa using hs₁ j x hx
    · intro m Z hZ
      have h₁ := ht₁ _ _ (Run.sub d hz hZ)
      rw [Fin.sum_univ_castSucc]
      have : (∑ i : Fin k, costs i.castSucc) + costs (Fin.last k) + m =
          (∑ i : Fin k, (costs ∘ Fin.castSucc) i) + (costs (Fin.last k) + m) := by
        simp only [Function.comp]; omega
      rw [this]
      exact h₁

/-- The route that places the argument registers `K, …, K+k-1` into positions
`0, …, k-1`. -/
def argRoute (K k : ℕ) (hk : k ≤ K) : Fin (2 * K + 2) → Fin (2 * K + 2) :=
  fun w => if h : w.val < k then ⟨K + w.val, by omega⟩ else w

/-- **Compilation.** Every evaluation in an environment of arity at most `K`
compiles into a register run of width `2K+2` with the same remainder cost. The
run returns the value of the term when it is a natural number. -/
theorem compile {P : Program} {K : ℕ} (hK : ∀ f, P.sig.arity f ≤ K) {n : ℕ}
    {ρ : Fin n → Val} {e : Tm P.sig n} {c : ℕ} {v : Val} (h : Eval P ρ e c v) :
    ∀ (hn : n ≤ K) (r : Registers (2 * K + 2)), Agree K hn r ρ →
      ∃ z, Run r c z ∧ ∀ x, v = .nat x → z = x := by
  induction h with
  | var ρ i =>
    intro hn r hr
    exact ⟨_, Run.ret r ⟨i, by have := i.isLt; omega⟩, fun x hx => hr i x hx⟩
  | tt ρ =>
    intro hn r hr
    exact ⟨_, Run.ret r ⟨0, by omega⟩, fun x hx => by cases hx⟩
  | ff ρ =>
    intro hn r hr
    exact ⟨_, Run.ret r ⟨0, by omega⟩, fun x hx => by cases hx⟩
  | @rem n ρ s t K' L x y hs ht hp ihs iht =>
    intro hn r hr
    obtain ⟨zs, hrs, hzs⟩ := ihs hn r hr
    have hzs' : zs = x := hzs x rfl
    subst hzs'
    set t0 : Fin (2 * K + 2) := ⟨2 * K, by omega⟩ with ht0
    set t1 : Fin (2 * K + 2) := ⟨2 * K + 1, by omega⟩ with ht1
    have h01 : t0 ≠ t1 := by simp [ht0, ht1]
    obtain ⟨zt, hrt, hzt⟩ := iht hn _ (hr.update t0 (by simp only [ht0]; omega) zs)
    have hzt' : zt = y := hzt y rfl
    subst hzt'
    set r₂ := Function.update (Function.update r t0 zs) t1 zt with hr₂
    have hr₂0 : r₂ t0 = zs := by
      rw [hr₂, Function.update_of_ne h01, Function.update_self]
    have hr₂1 : r₂ t1 = zt := by rw [hr₂, Function.update_self]
    have hm : Run r₂ (0 + 1) (zs % zt) := by
      have := Run.mod (r := r₂) t0 t1 t0 (by rw [hr₂1]; exact hp)
        (Run.ret (Function.update r₂ t0 (r₂ t0 % r₂ t1)) t0)
      simpa [hr₂0, hr₂1] using this
    have h₁ := Run.sub t1 hrt hm
    have h₂ := Run.sub t0 hrs h₁
    refine ⟨zs % zt, ?_, fun x hx => by cases hx; rfl⟩
    have he : K' + (L + (0 + 1)) = K' + L + 1 := by omega
    rw [he] at h₂
    exact h₂
  | eq0 hs ih =>
    intro hn r hr
    obtain ⟨z, h, _⟩ := ih hn r hr
    exact ⟨z, h, fun x hx => by cases hx⟩
  | eq1 hs ih =>
    intro hn r hr
    obtain ⟨z, h, _⟩ := ih hn r hr
    exact ⟨z, h, fun x hx => by cases hx⟩
  | iteT hc hs ihc ihs =>
    intro hn r hr
    obtain ⟨zc, hrc, _⟩ := ihc hn r hr
    set t0 : Fin (2 * K + 2) := ⟨2 * K, by omega⟩ with ht0
    obtain ⟨zs, hrs, hzs⟩ := ihs hn _ (hr.update t0 (by simp only [ht0]; omega) zc)
    exact ⟨zs, Run.sub t0 hrc hrs, hzs⟩
  | iteF hc ht ihc iht =>
    intro hn r hr
    obtain ⟨zc, hrc, _⟩ := ihc hn r hr
    set t0 : Fin (2 * K + 2) := ⟨2 * K, by omega⟩ with ht0
    obtain ⟨zt, hrt, hzt⟩ := iht hn _ (hr.update t0 (by simp only [ht0]; omega) zc)
    exact ⟨zt, Run.sub t0 hrc hrt, hzt⟩
  | @call n ρ f args costs vals body M v ha hb hc iha ihc =>
    intro hn r hr
    have hkf := hK f
    obtain ⟨r', hr', hslots, htrans⟩ :=
      args_run hn (P.sig.arity f) hkf costs vals (fun i r h => iha i hn r h) r hr
    set g := argRoute K (P.sig.arity f) hkf with hg
    have hag : Agree K hkf (r' ∘ g) vals := by
      intro i x hx
      have := hslots i x hx
      simpa [hg, argRoute, i.isLt] using this
    obtain ⟨z, hz, hzv⟩ := ihc hkf _ hag
    exact ⟨z, htrans _ _ (Run.route g hz), hzv⟩

/-- The input registers agree with the input environment `(a, b)`. -/
theorem agree_inputs {K : ℕ} (h2 : 2 ≤ K) (a b : ℕ) :
    Agree K h2 (inputs (2 * K + 2) a b) ![Val.nat a, Val.nat b] := by
  intro i x hx
  fin_cases i
  · simp at hx; simp [inputs, hx]
  · simp at hx; simp [inputs, hx]

/-- Every evaluation of the main term returning the natural number `z` compiles
into a register run of width `2K+2` returning `z`, with the same remainder cost. -/
theorem eval_run_val {P : Program} {K : ℕ} (hK : ∀ f, P.sig.arity f ≤ K) (h2 : 2 ≤ K)
    {a b c z : ℕ} (h : Eval P ![Val.nat a, Val.nat b] P.main c (.nat z)) :
    Run (inputs (2 * K + 2) a b) c z := by
  obtain ⟨z', hz', hzv⟩ := compile hK h h2 _ (agree_inputs h2 a b)
  rw [← hzv z rfl]
  exact hz'

theorem eval_run {P : Program} {K : ℕ} (hK : ∀ f, P.sig.arity f ≤ K) (h2 : 2 ≤ K)
    {a b c : ℕ} (h : Eval P ![Val.nat a, Val.nat b] P.main c (.nat 1)) :
    Run (inputs (2 * K + 2) a b) c 1 :=
  eval_run_val hK h2 h

/-! ## Provenance of the output -/

/-- The value returned by a register run is a value of a valid shape read off
its compiled code. -/
theorem run_shape_val {W a b n z : ℕ} (h : Run (inputs W a b) n z) :
    ∃ l : List (Instr W), l.length ≤ 5 * n + 1 ∧ (shapeOf l).length ≤ n ∧
      ∃ vals, runOps (shapeOf l) [a, b] = some vals ∧ z ∈ vals := by
  obtain ⟨code, i, r', hz, _, hmc, hlen, _, hex⟩ := Run.toCode h
  have hexec : exec (code ++ [.out i]) [inputs W a b] = some z := by
    rw [hex]; simp [exec, hz]
  have hag : List.Forall₂ (Agrees [a, b]) [inputs W a b] [s0 W] := by
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    intro w
    by_cases hw : w.val = 1 <;> simp [s0, inputs, hw]
  obtain ⟨ops, k, e, h1, h2, h3, h4⟩ := sim _ _ _ _ _ hag hexec
  have hshape : shapeOf (code ++ [.out i]) = ops := by
    simp only [shapeOf]; simp at h1; rw [h1]
  refine ⟨code ++ [.out i], ?_, ?_, [a, b] ++ e, ?_, List.mem_of_getElem? h3⟩
  · rcases hlen with h0 | h0
    · subst h0; simp
    · simp; omega
  · rw [hshape]; simp [modCount_append, modCount] at h4; omega
  · rw [hshape, h2]

/-- **Provenance.** Every natural-number output of a convergent evaluation on
`(a, b)` is a value produced by a valid shape whose length is at most the
evaluation's remainder cost. -/
theorem eval_shape_val {P : Program} {K : ℕ} (hK : ∀ f, P.sig.arity f ≤ K) (h2 : 2 ≤ K)
    {a b c z : ℕ} (h : Eval P ![Val.nat a, Val.nat b] P.main c (.nat z)) :
    ∃ S : Shape, S.length ≤ c ∧ ∃ vals, runOps S [a, b] = some vals ∧ z ∈ vals := by
  obtain ⟨l, _, hlen, vals, hrun, hz⟩ := run_shape_val (eval_run_val hK h2 h)
  exact ⟨shapeOf l, hlen, vals, hrun, hz⟩

/-! ## The Shape-Count Lemma -/

/-- The shapes read off codes of length at most `5c+1`. -/
def shapeSet (W c : ℕ) : Finset Shape := (codes W c).image shapeOf

theorem card_shapeSet_le (W c : ℕ) :
    (shapeSet W c).card ≤ (5 * c + 2) * Fintype.card (Instr W) ^ (5 * c + 1) :=
  Finset.card_image_le.trans (card_codes_le W c)

theorem card_shapeSet_le_pow (W c : ℕ) :
    (shapeSet W c).card ≤ (7 * Fintype.card (Instr W) ^ 5) ^ (c + 1) := by
  refine (card_shapeSet_le W c).trans ?_
  set A := Fintype.card (Instr W)
  have hA : 1 ≤ A := Fintype.card_pos_iff.mpr ⟨.call⟩
  have h7 : 5 * c + 2 ≤ 7 ^ (c + 1) := by
    have := one_add_mul_le_pow (show (-2 : ℤ) ≤ 6 by norm_num) (c + 1)
    have h' : (1 + ((c + 1 : ℕ) : ℤ) * 6) ≤ ((7 ^ (c + 1) : ℕ) : ℤ) := by
      push_cast; simpa [show (1 + 6 : ℤ) = 7 by norm_num] using this
    omega
  have hpow : A ^ (5 * c + 1) ≤ (A ^ 5) ^ (c + 1) := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right hA (by omega)
  calc (5 * c + 2) * A ^ (5 * c + 1) ≤ 7 ^ (c + 1) * (A ^ 5) ^ (c + 1) :=
        Nat.mul_le_mul h7 hpow
    _ = (7 * A ^ 5) ^ (c + 1) := (mul_pow _ _ _).symm

/-- **Shape-Count Lemma.** Fix `K ≥ 2`. For every program whose arities are at
most `K` and every `c`, every evaluation of the main term on an input
`a, b ≥ 2` that returns `1` with at most `c` remainder calls has a shape in
`shapeSet (2K+2) c` of length at most `c` that reaches `1` on `(a, b)`. This
finite set has at most `(7·A⁵)^(c+1)` elements (`card_shapeSet_le_pow`), where
`A = Fintype.card (Instr (2K+2))` depends only on `K`. -/
theorem eval_shape {P : Program} {K : ℕ} (hK : ∀ f, P.sig.arity f ≤ K) (h2 : 2 ≤ K)
    {a b c n : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hn : n ≤ c)
    (h : Eval P ![Val.nat a, Val.nat b] P.main n (.nat 1)) :
    ∃ S ∈ shapeSet (2 * K + 2) c, S.length ≤ c ∧ reaches1 S a b = true := by
  obtain ⟨l, hl, hlen, hreach⟩ := run_shape ha hb (eval_run hK h2 h)
  exact ⟨shapeOf l, Finset.mem_image_of_mem _ (mem_codes (by omega)), by omega, hreach⟩

/-! ## Counting consequences -/

open Classical in
/-- **Counting.** If every shape of length at most `c` reaches `1` on at most `B`
pairs of `box N`, then at most `(5c+2)·A^(5c+1)·B` pairs admit an evaluation of
the main term returning `1` with at most `c` remainder calls. -/
theorem card_eval_le (P : Program) {K : ℕ} (hK : ∀ f, P.sig.arity f ≤ K) (h2 : 2 ≤ K)
    (c N B : ℕ) (hB : ∀ S : Shape, S.length ≤ c → cnt N S ≤ B) :
    ((box N).filter (fun p => ∃ n ≤ c,
        Eval P ![Val.nat p.1, Val.nat p.2] P.main n (.nat 1))).card ≤
      (5 * c + 2) * Fintype.card (Instr (2 * K + 2)) ^ (5 * c + 1) * B := by
  refine le_trans (Finset.card_le_card ?_) (card_run_le (2 * K + 2) c N B hB)
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  obtain ⟨hbox, n, hn, he⟩ := hp
  exact ⟨hbox, n, hn, eval_run hK h2 he⟩

open Classical in
/-- **PSB implies a logarithmic lower bound for every program of bounded
arity.** If every shape of length at most `c₀ ln N` reaches `1` on at most
`N^(2-δ)` pairs of `box N` for all large `N`, then for each program of arity at
most `K` there is `r > 0` such that, eventually, at most `N^(2-δ/2)` pairs of
`box N` admit an evaluation returning `1` with at most `r ln N` remainder calls. -/
theorem eventually_card_eval_le (P : Program) {K : ℕ} (hK : ∀ f, P.sig.arity f ≤ K)
    (h2 : 2 ≤ K) {c₀ δ : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ)
    (hPSB : ∀ᶠ N : ℕ in Filter.atTop, ∀ S : Shape,
      (S.length : ℝ) ≤ c₀ * Real.log N → (cnt N S : ℝ) ≤ (N : ℝ) ^ (2 - δ)) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (((box N).filter (fun p => ∃ n : ℕ, (n : ℝ) ≤ r * Real.log N ∧
          Eval P ![Val.nat p.1, Val.nat p.2] P.main n (.nat 1))).card : ℝ) ≤
        (N : ℝ) ^ (2 - δ / 2) := by
  obtain ⟨r, hr, hev⟩ := eventually_card_run_le (2 * K + 2) hc₀ hδ hPSB
  refine ⟨r, hr, ?_⟩
  filter_upwards [hev] with N hN
  refine le_trans ?_ hN
  exact_mod_cast Finset.card_le_card (fun p hp => by
    simp only [Finset.mem_filter] at hp ⊢
    obtain ⟨hbox, n, hn, he⟩ := hp
    exact ⟨hbox, n, hn, eval_run hK h2 he⟩)

/-! ## Deciding coprimeness: the doubling argument -/

/-- Doubling a value: natural numbers are doubled, truth values are kept. -/
def dbl : Val → Val
  | .nat x => .nat (2 * x)
  | .bool b => .bool b

/-- **Doubling or a hit of `1`.** Take an evaluation in an environment with no
natural-number entry equal to `1`, and registers agreeing with it. Then either
the doubled evaluation exists (same term, same cost, doubled environment and
value) and its value is not `1`, or a register run of no greater cost returns
`1`. -/
theorem double_or_one {P : Program} {K : ℕ} (hK : ∀ f, P.sig.arity f ≤ K) {n : ℕ}
    {ρ : Fin n → Val} {e : Tm P.sig n} {c : ℕ} {v : Val} (h : Eval P ρ e c v) :
    (∀ i, ρ i ≠ .nat 1) → ∀ (hn : n ≤ K) (r : Registers (2 * K + 2)), Agree K hn r ρ →
      (Eval P (dbl ∘ ρ) e c (dbl v) ∧ v ≠ .nat 1) ∨ ∃ c' ≤ c, Run r c' 1 := by
  induction h with
  | var ρ i =>
    intro h1 hn r hr
    exact Or.inl ⟨Eval.var _ i, h1 i⟩
  | tt ρ => intro _ _ _ _; exact Or.inl ⟨Eval.tt _, by simp⟩
  | ff ρ => intro _ _ _ _; exact Or.inl ⟨Eval.ff _, by simp⟩
  | @rem n ρ s t K' L x y hs ht hp ihs iht =>
    intro h1 hn r hr
    rcases ihs h1 hn r hr with ⟨ds, hxs⟩ | ⟨c', hc', hrun⟩
    · rcases iht h1 hn r hr with ⟨dt, hyt⟩ | ⟨c', hc', hrun⟩
      · by_cases hxy : x % y = 1
        · obtain ⟨z, hz, hzv⟩ := compile hK (Eval.rem hs ht hp) hn r hr
          have : z = 1 := by rw [hzv _ rfl, hxy]
          exact Or.inr ⟨_, le_rfl, this ▸ hz⟩
        · left
          refine ⟨?_, fun h => hxy (by injection h)⟩
          have := Eval.rem ds dt (by omega)
          simpa [dbl, Nat.mul_mod_mul_left] using this
      · exact Or.inr ⟨c', by omega, hrun⟩
    · exact Or.inr ⟨c', by omega, hrun⟩
  | @eq0 n ρ s K' x hs ih =>
    intro h1 hn r hr
    rcases ih h1 hn r hr with ⟨ds, _⟩ | h
    · left
      refine ⟨?_, by simp⟩
      have := Eval.eq0 ds
      simpa [dbl] using this
    · exact Or.inr h
  | @eq1 n ρ s K' x hs ih =>
    intro h1 hn r hr
    rcases ih h1 hn r hr with ⟨ds, hx⟩ | h
    · left
      refine ⟨?_, by simp⟩
      have hx1 : x ≠ 1 := fun h => hx (by rw [h])
      have := Eval.eq1 ds
      have h2 : ¬ (2 * x = 1) := by omega
      simpa [dbl, hx1, h2] using this
    · exact Or.inr h
  | iteT hc hs ihc ihs =>
    intro h1 hn r hr
    rcases ihc h1 hn r hr with ⟨dc, _⟩ | ⟨c', hc', hrun⟩
    · rcases ihs h1 hn r hr with ⟨ds, hv⟩ | ⟨c', hc', hrun⟩
      · exact Or.inl ⟨Eval.iteT dc ds, hv⟩
      · exact Or.inr ⟨c', by omega, hrun⟩
    · exact Or.inr ⟨c', by omega, hrun⟩
  | iteF hc ht ihc iht =>
    intro h1 hn r hr
    rcases ihc h1 hn r hr with ⟨dc, _⟩ | ⟨c', hc', hrun⟩
    · rcases iht h1 hn r hr with ⟨dt, hv⟩ | ⟨c', hc', hrun⟩
      · exact Or.inl ⟨Eval.iteF dc dt, hv⟩
      · exact Or.inr ⟨c', by omega, hrun⟩
    · exact Or.inr ⟨c', by omega, hrun⟩
  | @call n ρ f args costs vals body M v ha hb hc iha ihc =>
    intro h1 hn r hr
    classical
    by_cases hall : ∀ i, Eval P (dbl ∘ ρ) (args i) (costs i) (dbl (vals i)) ∧ vals i ≠ .nat 1
    · have hkf := hK f
      obtain ⟨r', hr', hslots, htrans⟩ :=
        args_run hn (P.sig.arity f) hkf costs vals
          (fun i r h => compile hK (ha i) hn r h) r hr
      set g := argRoute K (P.sig.arity f) hkf with hg
      have hag : Agree K hkf (r' ∘ g) vals := by
        intro i x hx
        have := hslots i x hx
        simpa [hg, argRoute, i.isLt] using this
      rcases ihc (fun i => (hall i).2) hkf _ hag with ⟨db, hv⟩ | ⟨c', hc', hrun⟩
      · left
        exact ⟨Eval.call (fun i => (hall i).1) hb db, hv⟩
      · exact Or.inr ⟨_, by omega, htrans _ _ (Run.route g hrun)⟩
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      rcases iha i h1 hn r hr with ⟨di, hvi⟩ | ⟨c', hc', hrun⟩
      · exact absurd (hi di) hvi
      · have : costs i ≤ ∑ j, costs j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        exact Or.inr ⟨c', by omega, hrun⟩

/-- **A correct coprimeness decision produces `1`.** Suppose every convergent
computation of `P` on `(a, b)` answers whether `gcd a b = 1` (the
nondeterministic convention). If `P` answers "coprime" on `a, b ≥ 2` with `n`
remainder calls, then some register run of width `2K+2` on the inputs returns `1`
with at most `n` remainder calls. -/
theorem decide_run {P : Program} {K : ℕ} (hK : ∀ f, P.sig.arity f ≤ K) (h2 : 2 ≤ K)
    (hdec : ∀ a b c v, Eval P ![Val.nat a, Val.nat b] P.main c v →
      v = .bool (decide (Nat.gcd a b = 1)))
    {a b n : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : Eval P ![Val.nat a, Val.nat b] P.main n (.bool true)) :
    ∃ n' ≤ n, Run (inputs (2 * K + 2) a b) n' 1 := by
  have h1 : ∀ i, (![Val.nat a, Val.nat b] : Fin 2 → Val) i ≠ .nat 1 := by
    intro i; fin_cases i <;> simp <;> omega
  rcases double_or_one hK h h1 h2 _ (agree_inputs h2 a b) with ⟨hd, _⟩ | hrun
  · exfalso
    have he : (dbl ∘ ![Val.nat a, Val.nat b] : Fin 2 → Val) = ![Val.nat (2 * a), Val.nat (2 * b)] := by
      funext i; fin_cases i <;> rfl
    rw [he] at hd
    have := hdec _ _ _ _ hd
    simp only [dbl, Val.bool.injEq] at this
    have hc : Nat.gcd (2 * a) (2 * b) = 1 := of_decide_eq_true this.symm
    rw [Nat.gcd_mul_left] at hc
    omega
  · exact hrun

open Classical in
/-- **Counting for coprimeness decisions.** Under the hypotheses of `decide_run`,
if every shape of length at most `c` reaches `1` on at most `B` pairs of `box N`,
then at most `(5c+2)·A^(5c+1)·B` pairs admit a computation answering "coprime"
with at most `c` remainder calls. -/
theorem card_decide_le (P : Program) {K : ℕ} (hK : ∀ f, P.sig.arity f ≤ K) (h2 : 2 ≤ K)
    (hdec : ∀ a b c v, Eval P ![Val.nat a, Val.nat b] P.main c v →
      v = .bool (decide (Nat.gcd a b = 1)))
    (c N B : ℕ) (hB : ∀ S : Shape, S.length ≤ c → cnt N S ≤ B) :
    ((box N).filter (fun p => ∃ n ≤ c,
        Eval P ![Val.nat p.1, Val.nat p.2] P.main n (.bool true))).card ≤
      (5 * c + 2) * Fintype.card (Instr (2 * K + 2)) ^ (5 * c + 1) * B := by
  refine le_trans (Finset.card_le_card ?_) (card_run_le (2 * K + 2) c N B hB)
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  obtain ⟨hbox, n, hn, he⟩ := hp
  have hb : 2 ≤ p.2 ∧ p.2 < p.1 := by simp [box] at hbox; omega
  obtain ⟨n', hn', hrun⟩ := decide_run hK h2 hdec (by omega) hb.1 he
  exact ⟨hbox, n', by omega, hrun⟩

end ShortGCD.GeneralPrograms
