import ShortGCD.RegisterProgram
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Fixed-width register programs have few shapes

A *shape* is a straight-line remainder program with operands named by index:
running `S = [(i₁, j₁), …]` on `(a, b)` starts from the value list `[a, b]` and
appends `v[i] % v[j]` for each pair, failing on a missing index or a zero
divisor. `cnt N S` counts the pairs `2 ≤ b < a ≤ N` on which `S` produces the
value `1`.

The main theorem `card_run_le` bounds the number of pairs on which some run of
the width-`W` register semantics `RegisterProgram.Run` returns `1` with at most
`c` remainder calls by `(5c+2) · A^(5c+1) · B`, where `A` is the size of a fixed
finite instruction alphabet depending only on `W`, and `B` bounds `cnt N S` for
every shape of length at most `c`.

The proof compiles each run into a short linear code over that alphabet (routes
merged, zero-cost subcomputations absorbed, at most five instructions per
remainder call), and reads off the shape by executing the code symbolically,
with registers holding indices into the list of produced values.
-/

namespace ShortGCD.ShapeCount

open RegisterProgram

/-! ## Shapes -/

/-- A straight-line remainder program with operands named by index. -/
abbrev Shape := List (ℕ × ℕ)

/-- Run a shape on a value list, appending each remainder. -/
def runOps : Shape → List ℕ → Option (List ℕ)
  | [], v => some v
  | (i, j) :: ops, v =>
      match v[i]?, v[j]? with
      | some x, some y => if y = 0 then none else runOps ops (v ++ [x % y])
      | _, _ => none

/-- The shape is valid on `(a, b)` and some appended value is `1`. -/
def reaches1 (S : Shape) (a b : ℕ) : Bool :=
  match runOps S [a, b] with
  | some v => decide (1 ∈ v.drop 2)
  | none => false

/-- The pairs `2 ≤ b < a ≤ N`, written `(a, b)`. -/
def box (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 N) ×ˢ (Finset.Icc 2 N)).filter (fun p => p.2 < p.1)

/-- The number of pairs in `box N` on which the shape reaches `1`. -/
def cnt (N : ℕ) (S : Shape) : ℕ :=
  ((box N).filter (fun p => reaches1 S p.1 p.2 = true)).card

/-! ## Linear codes for register runs -/

/-- Instructions of a linear code: route registers, overwrite a register by a
remainder, open a subcomputation on a copy of the registers, close it by
writing register `i` into register `d` of the caller, or output a register. -/
inductive Instr (W : ℕ) where
  | route (g : Fin W → Fin W)
  | mod (i j d : Fin W)
  | call
  | ret (i d : Fin W)
  | out (i : Fin W)
  deriving Fintype, DecidableEq

variable {W : ℕ}

/-- Concrete execution on a stack of register files. -/
def exec : List (Instr W) → List (Registers W) → Option ℕ
  | .out i :: _, r :: _ => some (r i)
  | .route g :: p, r :: st => exec p ((r ∘ g) :: st)
  | .mod i j d :: p, r :: st =>
      if r j = 0 then none else exec p (Function.update r d (r i % r j) :: st)
  | .call :: p, r :: st => exec p (r :: r :: st)
  | .ret i d :: p, r :: r' :: st => exec p (Function.update r' d (r i) :: st)
  | _, _ => none

/-- Symbolic execution: registers hold indices into the produced-value list,
whose current length is `len`. Returns the emitted shape and the index of the
output. -/
def sexec : List (Instr W) → List (Fin W → ℕ) → ℕ → Option (Shape × ℕ)
  | .out i :: _, s :: _, _ => some ([], s i)
  | .route g :: p, s :: st, len => sexec p ((s ∘ g) :: st) len
  | .mod i j d :: p, s :: st, len =>
      (sexec p (Function.update s d len :: st) (len + 1)).map
        (fun q => ((s i, s j) :: q.1, q.2))
  | .call :: p, s :: st, len => sexec p (s :: s :: st) len
  | .ret i d :: p, s :: s' :: st, len => sexec p (Function.update s' d (s i) :: st) len
  | _, _, _ => none

/-- Number of remainder instructions. -/
def modCount : List (Instr W) → ℕ
  | [] => 0
  | .mod _ _ _ :: p => modCount p + 1
  | _ :: p => modCount p

theorem modCount_append (l₁ l₂ : List (Instr W)) :
    modCount (l₁ ++ l₂) = modCount l₁ + modCount l₂ := by
  induction l₁ with
  | nil => simp [modCount]
  | cons x p ih => cases x <;> simp [modCount, ih]; omega

/-! ## Symbolic execution tracks concrete execution -/

/-- Register file `r` agrees with symbolic file `s` on the value list `vals`. -/
def Agrees (vals : List ℕ) (r : Registers W) (s : Fin W → ℕ) : Prop :=
  ∀ w, vals[s w]? = some (r w)

theorem Agrees.append {vals e : List ℕ} {r : Registers W} {s : Fin W → ℕ}
    (h : Agrees vals r s) : Agrees (vals ++ e) r s := by
  intro w
  have hw := h w
  have hlt : s w < vals.length := (List.getElem?_eq_some_iff.1 hw).1
  rw [List.getElem?_append_left hlt]
  exact hw

theorem sim : ∀ (l : List (Instr W)) (st : List (Registers W))
    (sst : List (Fin W → ℕ)) (vals : List ℕ) (z : ℕ),
    List.Forall₂ (Agrees vals) st sst → exec l st = some z →
    ∃ ops k e, sexec l sst vals.length = some (ops, k) ∧
      runOps ops vals = some (vals ++ e) ∧ (vals ++ e)[k]? = some z ∧
      ops.length ≤ modCount l := by
  intro l
  induction l with
  | nil => intro st sst vals z _ h; simp [exec] at h
  | cons x p ih =>
    intro st sst vals z hag hex
    rcases st with _ | ⟨r, st⟩
    · cases x <;> simp [exec] at hex
    rcases sst with _ | ⟨s, sst⟩
    · cases hag
    obtain ⟨hr, hrest⟩ := List.forall₂_cons.1 hag
    cases x with
    | out i =>
      simp only [exec, Option.some.injEq] at hex
      subst hex
      exact ⟨[], s i, [], by simp [sexec], by simp [runOps], by simpa using hr i,
        by simp⟩
    | route g =>
      simp only [exec] at hex
      have htop : Agrees vals (r ∘ g) (s ∘ g) := fun w => hr (g w)
      obtain ⟨ops, k, e, h1, h2, h3, h4⟩ :=
        ih _ _ vals z (List.Forall₂.cons htop hrest) hex
      exact ⟨ops, k, e, by simpa [sexec] using h1, h2, h3, by simpa [modCount] using h4⟩
    | mod i j d =>
      simp only [exec] at hex
      split_ifs at hex with hz
      set v₁ := vals ++ [r i % r j] with hv₁
      have htop : Agrees v₁ (Function.update r d (r i % r j))
          (Function.update s d vals.length) := by
        intro w
        by_cases hw : w = d
        · subst hw; simp [hv₁]
        · simp only [Function.update_of_ne hw]
          exact (Agrees.append (e := [r i % r j]) hr) w
      have hag₁ : List.Forall₂ (Agrees v₁) (Function.update r d (r i % r j) :: st)
          (Function.update s d vals.length :: sst) :=
        List.Forall₂.cons htop (hrest.imp (fun _ _ h => h.append))
      obtain ⟨ops, k, e, h1, h2, h3, h4⟩ := ih _ _ v₁ z hag₁ hex
      have hlen : v₁.length = vals.length + 1 := by simp [hv₁]
      rw [hlen] at h1
      refine ⟨(s i, s j) :: ops, k, [r i % r j] ++ e, ?_, ?_, ?_, ?_⟩
      · simp [sexec, h1]
      · simp only [runOps, hr i, hr j, hz]
        simp only [ite_false]
        rw [h2, hv₁, List.append_assoc]
      · rw [← List.append_assoc]; exact h3
      · simp [modCount, h4]
    | call =>
      simp only [exec] at hex
      obtain ⟨ops, k, e, h1, h2, h3, h4⟩ :=
        ih _ _ vals z (List.Forall₂.cons hr (List.Forall₂.cons hr hrest)) hex
      exact ⟨ops, k, e, by simpa [sexec] using h1, h2, h3, by simpa [modCount] using h4⟩
    | ret i d =>
      rcases st with _ | ⟨r', st⟩
      · simp [exec] at hex
      rcases sst with _ | ⟨s', sst⟩
      · cases hrest
      obtain ⟨hr', hrest'⟩ := List.forall₂_cons.1 hrest
      simp only [exec] at hex
      have htop : Agrees vals (Function.update r' d (r i)) (Function.update s' d (s i)) := by
        intro w
        by_cases hw : w = d
        · subst hw; simpa using hr i
        · simpa [Function.update_of_ne hw] using hr' w
      obtain ⟨ops, k, e, h1, h2, h3, h4⟩ :=
        ih _ _ vals z (List.Forall₂.cons htop hrest') hex
      exact ⟨ops, k, e, by simpa [sexec] using h1, h2, h3, by simpa [modCount] using h4⟩

/-! ## Compiling runs into short codes -/

theorem Run.toCode {r : Registers W} {n z : ℕ} (h : Run r n z) :
    ∃ (code : List (Instr W)) (i : Fin W) (r' : Registers W),
      r' i = z ∧ (code = [] → r' = r) ∧ modCount code ≤ n ∧
      (code = [] ∨ code.length + 3 ≤ 5 * n) ∧
      (code = [] ∨ ∃ g body, code = .route g :: body) ∧
      ∀ p st, exec (code ++ p) (r :: st) = exec p (r' :: st) := by
  induction h with
  | ret r i =>
    exact ⟨[], i, r, rfl, fun _ => rfl, by simp [modCount], Or.inl rfl, Or.inl rfl,
      fun _ _ => rfl⟩
  | @mod r i j dest hp n z _ ih =>
    obtain ⟨code, i', r', hz, _, hmc, hlen, _, hex⟩ := ih
    refine ⟨.route id :: .mod i j dest :: code, i', r', hz, by simp, ?_, ?_,
      Or.inr ⟨id, _, rfl⟩, ?_⟩
    · simp [modCount]; omega
    · right; rcases hlen with h | h
      · subst h; simp
      · simp; omega
    · intro p st
      have hne : r j ≠ 0 := Nat.pos_iff_ne_zero.mp hp
      simp only [List.cons_append, exec]
      simpa [hne] using hex p st
  | @route r f n z _ ih =>
    obtain ⟨code, i, r', hz, hnil, hmc, hlen, hst, hex⟩ := ih
    rcases hst with h0 | ⟨g, body, rfl⟩
    · subst h0
      have := hnil rfl
      subst this
      exact ⟨[], f i, r, hz, fun _ => rfl, by simp [modCount], Or.inl rfl, Or.inl rfl,
        fun _ _ => rfl⟩
    · refine ⟨.route (f ∘ g) :: body, i, r', hz, by simp, by simpa [modCount] using hmc,
        by simpa using hlen, Or.inr ⟨_, _, rfl⟩, ?_⟩
      intro p st
      have := hex p st
      simp only [List.cons_append, exec] at this ⊢
      exact this
  | @sub r dest n m z y _ _ ih₁ ih₂ =>
    obtain ⟨c₁, i₁, r₁, hz₁, hnil₁, hmc₁, hlen₁, hst₁, hex₁⟩ := ih₁
    obtain ⟨c₂, i₂, r₂, hz₂, hnil₂, hmc₂, hlen₂, hst₂, hex₂⟩ := ih₂
    rcases hst₁ with h0 | ⟨g₁, body₁, hc₁⟩
    · -- zero-cost subcomputation: a route
      subst h0
      have hr₁ : r₁ = r := hnil₁ rfl
      have hy : r i₁ = y := hr₁ ▸ hz₁
      set f : Fin W → Fin W := Function.update id dest i₁ with hfdef
      have hf : Function.update r dest y = r ∘ f := by
        funext w
        by_cases hw : w = dest
        · subst hw; simp [hfdef, hy]
        · simp [hfdef, Function.update_of_ne hw]
      rcases hst₂ with h0 | ⟨g, body, rfl⟩
      · subst h0
        have := hnil₂ rfl
        subst this
        refine ⟨[], f i₂, r, ?_, fun _ => rfl, by simp [modCount], Or.inl rfl, Or.inl rfl,
          fun _ _ => rfl⟩
        rw [← hz₂, hf]; rfl
      · refine ⟨.route (f ∘ g) :: body, i₂, r₂, hz₂, by simp, ?_, ?_, Or.inr ⟨_, _, rfl⟩, ?_⟩
        · simp [modCount] at hmc₂ ⊢; omega
        · right; rcases hlen₂ with h | h
          · simp at h
          · simp at h ⊢; omega
        · intro p st
          have := hex₂ p st
          rw [hf] at this
          simp only [List.cons_append, exec] at this ⊢
          exact this
    · have hne₁ : c₁ ≠ [] := by simp [hc₁]
      have hl₁ : c₁.length + 3 ≤ 5 * n := hlen₁.resolve_left hne₁
      rcases hst₂ with h0 | ⟨g₂, body₂, hc₂⟩
      · subst h0
        have hr₂ := hnil₂ rfl
        subst hr₂
        by_cases hi : i₂ = dest
        · subst hi
          refine ⟨c₁, i₁, r₁, ?_, fun h => absurd h hne₁, by omega, Or.inr (by omega),
            Or.inr ⟨g₁, body₁, hc₁⟩, hex₁⟩
          simp at hz₂; rw [hz₁, hz₂]
        · refine ⟨[], i₂, r, ?_, fun _ => rfl, by simp [modCount], Or.inl rfl, Or.inl rfl,
            fun _ _ => rfl⟩
          simpa [Function.update_of_ne hi] using hz₂
      · have hne₂ : c₂ ≠ [] := by simp [hc₂]
        have hl₂ : c₂.length + 3 ≤ 5 * m := hlen₂.resolve_left hne₂
        refine ⟨.route id :: .call :: (c₁ ++ .ret i₁ dest :: c₂), i₂, r₂, hz₂, by simp,
          ?_, ?_, Or.inr ⟨id, _, rfl⟩, ?_⟩
        · simp [modCount, modCount_append]; omega
        · right; simp; omega
        · intro p st
          have h1 := hex₁ (.ret i₁ dest :: (c₂ ++ p)) (r :: st)
          have h2 := hex₂ p st
          simp only [List.cons_append, List.append_assoc, exec, Function.comp_id] at h1 h2 ⊢
          rw [h1, hz₁]
          exact h2

/-! ## From runs to shapes -/

/-- Initial symbolic registers for `inputs W a b`. -/
def s0 (W : ℕ) : Fin W → ℕ := fun i => if i.val = 1 then 1 else 0

/-- The shape read off a code from the input registers. -/
def shapeOf (l : List (Instr W)) : Shape :=
  match sexec l [s0 W] 2 with
  | some q => q.1
  | none => []

theorem run_shape {a b n : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : Run (inputs W a b) n 1) :
    ∃ l : List (Instr W), l.length ≤ 5 * n + 1 ∧ (shapeOf l).length ≤ n ∧
      reaches1 (shapeOf l) a b = true := by
  obtain ⟨code, i, r', hz, _, hmc, hlen, _, hex⟩ := Run.toCode h
  have hexec : exec (code ++ [.out i]) [inputs W a b] = some 1 := by
    rw [hex]; simp [exec, hz]
  have hag : List.Forall₂ (Agrees [a, b]) [inputs W a b] [s0 W] := by
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    intro w
    by_cases hw : w.val = 1 <;> simp [s0, inputs, hw]
  obtain ⟨ops, k, e, h1, h2, h3, h4⟩ := sim _ _ _ _ _ hag hexec
  have hshape : shapeOf (code ++ [.out i]) = ops := by
    simp only [shapeOf]; simp at h1; rw [h1]
  refine ⟨code ++ [.out i], ?_, ?_, ?_⟩
  · rcases hlen with h0 | h0
    · subst h0; simp
    · simp; omega
  · rw [hshape]; simp [modCount_append, modCount] at h4; omega
  · rw [hshape]
    simp only [reaches1, h2]
    simp only [decide_eq_true_eq]
    have hk : 2 ≤ k := by
      by_contra hk
      interval_cases k <;> simp at h3 <;> omega
    have : e[k - 2]? = some 1 := by
      rw [List.getElem?_append_right (by simp; omega)] at h3
      simpa using h3
    simpa using List.mem_of_getElem? this

/-! ## Counting -/

/-- All codes of length at most `5c+1`. -/
def codes (W c : ℕ) : Finset (List (Instr W)) :=
  (Finset.range (5 * c + 2)).biUnion
    (fun k => Finset.univ.image (fun f : Fin k → Instr W => List.ofFn f))

theorem mem_codes {c : ℕ} {l : List (Instr W)} (hl : l.length ≤ 5 * c + 1) :
    l ∈ codes W c := by
  simp only [codes, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact ⟨l.length, by omega, fun i => l[i], List.ofFn_getElem⟩

theorem card_codes_le (W c : ℕ) :
    (codes W c).card ≤ (5 * c + 2) * Fintype.card (Instr W) ^ (5 * c + 1) := by
  have hA : 1 ≤ Fintype.card (Instr W) := Fintype.card_pos_iff.mpr ⟨.call⟩
  calc (codes W c).card
      ≤ ∑ k ∈ Finset.range (5 * c + 2),
          (Finset.univ.image (fun f : Fin k → Instr W => List.ofFn f)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (5 * c + 2), Fintype.card (Instr W) ^ (5 * c + 1) := by
        apply Finset.sum_le_sum
        intro k hk
        calc (Finset.univ.image (fun f : Fin k → Instr W => List.ofFn f)).card
            ≤ (Finset.univ : Finset (Fin k → Instr W)).card := Finset.card_image_le
          _ = Fintype.card (Instr W) ^ k := by simp
          _ ≤ Fintype.card (Instr W) ^ (5 * c + 1) :=
              Nat.pow_le_pow_right hA (by simp at hk; omega)
    _ = (5 * c + 2) * Fintype.card (Instr W) ^ (5 * c + 1) := by simp

open Classical in
/-- **Shape-count theorem for register programs.** If every shape of length at
most `c` reaches `1` on at most `B` pairs of `box N`, then at most
`(5c+2)·A^(5c+1)·B` pairs admit a width-`W` run returning `1` with at most `c`
remainder calls, where `A = Fintype.card (Instr W)` depends only on `W`. -/
theorem card_run_le (W c N B : ℕ) (hB : ∀ S : Shape, S.length ≤ c → cnt N S ≤ B) :
    ((box N).filter (fun p => ∃ n ≤ c, Run (inputs W p.1 p.2) n 1)).card ≤
      (5 * c + 2) * Fintype.card (Instr W) ^ (5 * c + 1) * B := by
  set T := (codes W c).filter (fun l => (shapeOf l).length ≤ c)
  have hsub : (box N).filter (fun p => ∃ n ≤ c, Run (inputs W p.1 p.2) n 1) ⊆
      T.biUnion (fun l => (box N).filter (fun p => reaches1 (shapeOf l) p.1 p.2 = true)) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hbox, n, hn, hrun⟩ := hp
    have hb : 2 ≤ p.2 ∧ p.2 < p.1 := by
      simp [box] at hbox; omega
    obtain ⟨l, hl, hlen, hreach⟩ := run_shape (by omega) hb.1 hrun
    exact Finset.mem_biUnion.2 ⟨l, Finset.mem_filter.2 ⟨mem_codes (by omega), by omega⟩,
      Finset.mem_filter.2 ⟨hbox, hreach⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ l ∈ T, cnt N (shapeOf l) := Finset.card_biUnion_le
    _ ≤ ∑ _l ∈ T, B := by
        apply Finset.sum_le_sum
        intro l hl
        exact hB _ (Finset.mem_filter.1 hl).2
    _ = T.card * B := by simp
    _ ≤ (codes W c).card * B := Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ ≤ _ := Nat.mul_le_mul_right _ (card_codes_le W c)

open Classical in
/-- The same bound for the full program `Accepts`, whose verification wrapper
adds two remainder calls. -/
theorem card_accepts_le (W c N B : ℕ) (hB : ∀ S : Shape, S.length ≤ c → cnt N S ≤ B) :
    ((box N).filter (fun p => ∃ n ≤ c + 2, Accepts W p.1 p.2 n 1)).card ≤
      (5 * c + 2) * Fintype.card (Instr W) ^ (5 * c + 1) * B := by
  refine le_trans (Finset.card_le_card ?_) (card_run_le W c N B hB)
  rintro ⟨a, b⟩ hp
  simp only [Finset.mem_filter] at hp ⊢
  obtain ⟨hbox, n, hn, hacc⟩ := hp
  refine ⟨hbox, ?_⟩
  cases hacc with
  | zero => simp [box] at hbox
  | checked _ hrun _ _ _ => exact ⟨_, by omega, hrun⟩

/-! ## The asymptotic consequence of a per-shape bound -/

/-- `K (log N + 1) ≤ N^a` eventually. -/
theorem eventually_log_le_rpow {K a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) :
    ∀ᶠ N : ℕ in Filter.atTop, K * (Real.log N + 1) ≤ (N : ℝ) ^ a := by
  have hε : (0 : ℝ) < 1 / (2 * (K + 1)) := by positivity
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, ‖Real.log x‖ ≤ 1 / (2 * (K + 1)) * ‖x ^ a‖ :=
    (isLittleO_log_rpow_atTop ha).bound hε
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, 2 * K ≤ x ^ a :=
    (tendsto_rpow_atTop ha).eventually_ge_atTop _
  have h3 : ∀ᶠ x : ℝ in Filter.atTop, 0 ≤ x := Filter.eventually_ge_atTop 0
  have h := (h1.and (h2.and h3))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with N hN
  obtain ⟨hlog, hbig, hpos⟩ := hN
  have hxa : 0 ≤ (N : ℝ) ^ a := Real.rpow_nonneg hpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hxa] at hlog
  have hl : Real.log N ≤ 1 / (2 * (K + 1)) * (N : ℝ) ^ a := le_trans (le_abs_self _) hlog
  have : K * Real.log N ≤ (N : ℝ) ^ a / 2 := by
    calc K * Real.log N ≤ K * (1 / (2 * (K + 1)) * (N : ℝ) ^ a) :=
          mul_le_mul_of_nonneg_left hl hK
      _ = (K / (K + 1)) * ((N : ℝ) ^ a / 2) := by field_simp
      _ ≤ 1 * ((N : ℝ) ^ a / 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_one (by positivity)]; linarith
      _ = (N : ℝ) ^ a / 2 := one_mul _
  nlinarith

open Classical in
/-- **PSB implies a logarithmic lower bound for every fixed width.** If every
shape of length at most `c₀ ln N` reaches `1` on at most `N^(2-δ)` pairs of
`box N` for all large `N`, then for each width `W` there is `r > 0` such that
eventually at most `N^(2-δ/2)` pairs of `box N` admit a run returning `1` with at
most `r ln N` remainder calls. -/
theorem eventually_card_run_le (W : ℕ) {c₀ δ : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ)
    (hPSB : ∀ᶠ N : ℕ in Filter.atTop, ∀ S : Shape,
      (S.length : ℝ) ≤ c₀ * Real.log N → (cnt N S : ℝ) ≤ (N : ℝ) ^ (2 - δ)) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (((box N).filter (fun p => ∃ n : ℕ, (n : ℝ) ≤ r * Real.log N ∧
          Run (inputs W p.1 p.2) n 1)).card : ℝ) ≤ (N : ℝ) ^ (2 - δ / 2) := by
  set A : ℕ := Fintype.card (Instr W) with hAdef
  have hA1 : 1 ≤ A := Fintype.card_pos_iff.mpr ⟨.call⟩
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA1
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hAr
  set r : ℝ := min c₀ (δ / (20 * (Real.log A + 1))) with hrdef
  have hr : 0 < r := lt_min hc₀ (by positivity)
  have hrc : r ≤ c₀ := min_le_left _ _
  have hrA : 5 * r * Real.log A ≤ δ / 4 := by
    have h := min_le_right c₀ (δ / (20 * (Real.log A + 1)))
    have : 5 * r * Real.log A ≤ 5 * (δ / (20 * (Real.log A + 1))) * Real.log A := by
      apply mul_le_mul_of_nonneg_right _ hlogA; linarith
    refine le_trans this ?_
    rw [show 5 * (δ / (20 * (Real.log A + 1))) * Real.log A
        = δ / 4 * (Real.log A / (Real.log A + 1)) by field_simp; ring]
    have : Real.log A / (Real.log A + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  refine ⟨r, hr, ?_⟩
  have hpoly := eventually_log_le_rpow (K := (5 * r + 2) * A) (a := δ / 4)
    (by positivity) (by positivity)
  filter_upwards [hPSB, hpoly, Filter.eventually_ge_atTop 1] with N hN hK hN1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hL : 0 ≤ Real.log N := Real.log_nonneg hNr
  set c : ℕ := ⌊r * Real.log N⌋₊ with hcdef
  have hc : (c : ℝ) ≤ r * Real.log N := Nat.floor_le (by positivity)
  set B : ℕ := ⌊(N : ℝ) ^ (2 - δ)⌋₊ with hBdef
  have hB : ∀ S : Shape, S.length ≤ c → cnt N S ≤ B := by
    intro S hS
    apply Nat.le_floor
    apply hN
    have : (S.length : ℝ) ≤ c := by exact_mod_cast hS
    nlinarith
  have hmain := card_run_le W c N B hB
  have hsub : (box N).filter (fun p => ∃ n : ℕ, (n : ℝ) ≤ r * Real.log N ∧
      Run (inputs W p.1 p.2) n 1) ⊆
      (box N).filter (fun p => ∃ n ≤ c, Run (inputs W p.1 p.2) n 1) := by
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    obtain ⟨hbox, n, hn, hrun⟩ := hp
    exact ⟨hbox, n, Nat.le_floor hn, hrun⟩
  have hcard := (Finset.card_le_card hsub).trans hmain
  have hBr : (B : ℝ) ≤ (N : ℝ) ^ (2 - δ) := Nat.floor_le (by positivity)
  -- A^(5c) ≤ N^(δ/4)
  have hpow : (A : ℝ) ^ (5 * c) ≤ (N : ℝ) ^ (δ / 4) := by
    have hApos : (0 : ℝ) < A := by linarith
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hApos, Real.rpow_def_of_pos hNpos]
    apply Real.exp_le_exp.mpr
    push_cast
    have : Real.log A * (5 * (c : ℝ)) ≤ Real.log A * (5 * (r * Real.log N)) :=
      mul_le_mul_of_nonneg_left (by linarith) hlogA
    nlinarith
  -- (5c+2) A ≤ N^(δ/4)
  have hlin : ((5 * c + 2 : ℕ) : ℝ) * A ≤ (N : ℝ) ^ (δ / 4) := by
    refine le_trans ?_ hK
    push_cast
    have hA0 : (0 : ℝ) ≤ A := by linarith
    nlinarith
  calc (((box N).filter (fun p => ∃ n : ℕ, (n : ℝ) ≤ r * Real.log N ∧
          Run (inputs W p.1 p.2) n 1)).card : ℝ)
      ≤ (((5 * c + 2) * A ^ (5 * c + 1) * B : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (((5 * c + 2 : ℕ) : ℝ) * A) * (A : ℝ) ^ (5 * c) * B := by push_cast; ring
    _ ≤ (N : ℝ) ^ (δ / 4) * (N : ℝ) ^ (δ / 4) * (N : ℝ) ^ (2 - δ) := by
        gcongr
    _ = (N : ℝ) ^ (2 - δ / 2) := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; ring_nf

end ShortGCD.ShapeCount
