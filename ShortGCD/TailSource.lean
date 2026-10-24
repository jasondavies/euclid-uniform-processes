module

public import ShortGCD.RegisterProgram
public import ShortGCD.TailAsymptotic

@[expose] public section

/-! The bounded-memory gcd program as a register program in the book's sense
(`Register.Program`: §2F, with the nondeterminism of §2E), with `w + 2` registers and only
prime terms.

Registers `u₀, u₁` hold the inputs `a, b`, and `u_{2+j}` is work register `j`; the initial
values are the explicit function `(a, b, a, b, a, …, a)` of the inputs, as (2F-1) allows.
Line `head` returns `u₀` if `eq0(u₁)`, and otherwise passes to the main line `run`. There the
program may assign `rem(uᵢ, uⱼ)` to any work register, or pass to the verification of a
nonzero work register `uᵢ`, which halts with `uᵢ` after `u₀ := rem(u₀, uᵢ)` and
`u₁ := rem(u₁, uᵢ)` if both are zero. The main line never writes `u₀, u₁`; only verification
does, after which the inputs are not needed. A zero candidate and a failed check go to the
line `reject`, which loops. Every remainder evaluation is charged once.

`executes_iff` proves exact-cost equivalence with the generator and its verifier
(`TailProgram.Accepts`). For the costs it replays generator runs, including their cost-free
relabellings of the registers, by single-register commands (`run_trace_relabel`).
-/
namespace ShortGCD.TailSource
open TailProgram Register

/-- The lines of the program, by name. -/
inductive Label (w : ℕ) where
  | head
  | ret
  | run
  | reject
  | left (i : Fin w)
  | leftTest (i : Fin w)
  | right (i : Fin w)
  | rightTest (i : Fin w)
  | done (i : Fin w)
  deriving DecidableEq, Fintype

/-- The input registers `u₀, u₁` and the work register `u_{2+j}`. -/
def inA {w} : Fin (2+w) := Fin.castAdd w 0
def inB {w} : Fin (2+w) := Fin.castAdd w 1
def work {w} (j : Fin w) : Fin (2+w) := Fin.natAdd 2 j

/-- The commands of the main line: any remainder assignment between work registers, or the
verification of a nonzero candidate. -/
def mainCmds (w : ℕ) : List (Cmd (2+w) (Label w)) :=
  (List.finRange w).flatMap (fun i => (List.finRange w).flatMap fun j =>
    (List.finRange w).map fun d => .assign (work d) (.rem (work i) (work j)) .run) ++
  (List.finRange w).map fun i => .branch (.eq0 (work i)) .reject (.left i)

/-- The lines of the program. -/
def lines (w : ℕ) : Label w → Line (2+w) (Label w)
  | .head => .cmds [.branch (.eq0 inB) .ret .run]
  | .ret => .halt (.reg inA)
  | .run => .cmds (mainCmds w)
  | .reject => .cmds [.branch .tt .reject .reject]
  | .left i => .cmds [.assign inA (.rem inA (work i)) (.leftTest i)]
  | .leftTest i => .cmds [.branch (.eq0 inA) (.right i) .reject]
  | .right i => .cmds [.assign inB (.rem inB (work i)) (.rightTest i)]
  | .rightTest i => .cmds [.branch (.eq0 inB) (.done i) .reject]
  | .done i => .halt (.reg (work i))

/-- The register program, with its lines numbered from `head = 0`. -/
noncomputable def program (w : ℕ) : Program (2+w) := ofLabels (lines w) .head

/-- The initial registers `(a, b, a, b, a, …, a)`. -/
def init (w a b : ℕ) : Fin (2+w) → ℕ := fun x => if x.val = 1 ∨ x.val = 3 then b else a

/-- A convergent computation of the program on `(a, b)` returns `z` with `c` remainder
calls. -/
def Executes (w a b c z : ℕ) : Prop := (program w).Returns (init w a b) c z

lemma total_registers (p : ℕ) : 2+Fixed.width p = 4^p+7 := by
  rw [Fixed.width_eq]; omega

/-! ## Correspondence with the generator -/

lemma work_injective {w} : Function.Injective (work (w := w)) :=
  Fin.natAdd_injective w 2

lemma work_ne_inA {w} (j : Fin w) : work j ≠ inA := by
  simp only [work, inA, ne_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]; omega

lemma work_ne_inB {w} (j : Fin w) : work j ≠ inB := by
  simp only [work, inB, ne_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]; omega

lemma inA_ne_inB {w} : (inA : Fin (2+w)) ≠ inB := by
  simp [inA, inB, Fin.ext_iff]

lemma update_work {w} (u : Fin (2+w) → ℕ) (d : Fin w) (v : ℕ) :
    Function.update u (work d) v ∘ work = Function.update (u ∘ work) d v :=
  Function.update_comp_eq_of_injective u work_injective d v

lemma init_work (w a b : ℕ) : init w a b ∘ work = inputs w a b := by
  funext j
  have h : (2+(j:ℕ) = 1 ∨ 2+(j:ℕ) = 3) ↔ (j:ℕ) = 1 := by omega
  simp only [Function.comp, init, inputs, work, Fin.val_natAdd, h]

abbrev State (w : ℕ) := Label w × (Fin (2+w) → ℕ)

/-- Backward assertion: what a convergent computation from a state, returning `z` with
`c` further remainder calls, tells us about that state. -/
def Reads {w} (s : State w) (c z : ℕ) : Prop :=
  let u := s.2
  match s.1 with
  | .head => (u inB = 0 ∧ c = 0 ∧ z = u inA) ∨
      (0 < u inB ∧ ∃ n, Run (u ∘ work) n z ∧ c = n+2 ∧ 0 < z ∧ u inA % z = 0 ∧ u inB % z = 0)
  | .ret => c = 0 ∧ z = u inA
  | .run => ∃ n, Run (u ∘ work) n z ∧ c = n+2 ∧ 0 < z ∧ u inA % z = 0 ∧ u inB % z = 0
  | .reject => False
  | .left i => z = u (work i) ∧ c = 2 ∧ 0 < z ∧ u inA % z = 0 ∧ u inB % z = 0
  | .leftTest i => z = u (work i) ∧ c = 1 ∧ 0 < z ∧ u inA = 0 ∧ u inB % z = 0
  | .right i => z = u (work i) ∧ c = 1 ∧ 0 < z ∧ u inB % z = 0
  | .rightTest i => z = u (work i) ∧ c = 0 ∧ u inB = 0
  | .done i => z = u (work i) ∧ c = 0

lemma step_reads {w c k z} {s t : State w} (h : Step (lines w) s c t) (ht : Reads t k z) :
    Reads s (c+k) z := by
  cases h with
  | @assign l u cs x e l' v hl hc hv =>
    cases l <;> simp only [lines, reduceCtorEq, Line.cmds.injEq] at hl <;> subst hl <;>
      simp only [mainCmds, List.mem_append, List.mem_flatMap, List.mem_finRange, List.mem_map,
        List.mem_singleton, true_and, Cmd.assign.injEq, reduceCtorEq, and_false, exists_false,
        or_false] at hc
    case run =>
      obtain ⟨i, j, d, rfl, rfl, rfl⟩ := hc
      simp only [Term.value] at hv
      split_ifs at hv with hj
      cases hv
      obtain ⟨n, hn, hk, hz, ha, hb⟩ := ht
      simp only [Function.update_of_ne (work_ne_inA d).symm,
        Function.update_of_ne (work_ne_inB d).symm, update_work] at hn ha hb
      exact ⟨n+1, .mod i j d (Nat.pos_of_ne_zero hj) hn, by simp [Term.calls]; omega, hz, ha, hb⟩
    case left i =>
      obtain ⟨rfl, rfl, rfl⟩ := hc
      simp only [Term.value] at hv
      split_ifs at hv with hi
      cases hv
      obtain ⟨hz, hk, hpos, h0, hb⟩ := ht
      simp only [Function.update_self, Function.update_of_ne (work_ne_inA i),
        Function.update_of_ne inA_ne_inB.symm] at hz h0 hb
      subst hz
      exact ⟨rfl, by simp [Term.calls]; omega, hpos, h0, hb⟩
    case right i =>
      obtain ⟨rfl, rfl, rfl⟩ := hc
      simp only [Term.value] at hv
      split_ifs at hv with hi
      cases hv
      obtain ⟨hz, hk, h0⟩ := ht
      simp only [Function.update_self, Function.update_of_ne (work_ne_inB i)] at hz h0
      subst hz
      exact ⟨rfl, by simp [Term.calls]; omega, Nat.pos_of_ne_zero hi, h0⟩
  | @branch l u cs e l' l'' hl hc =>
    cases l <;> simp only [lines, reduceCtorEq, Line.cmds.injEq] at hl <;> subst hl <;>
      simp only [mainCmds, List.mem_append, List.mem_flatMap, List.mem_finRange, List.mem_map,
        List.mem_singleton, true_and, Cmd.branch.injEq, reduceCtorEq, and_false, exists_false,
        false_or] at hc
    case head =>
      obtain ⟨rfl, rfl, rfl⟩ := hc
      by_cases hb : u inB = 0
      · simp only [Test.value, hb, decide_true, Bool.cond_true, Reads] at ht
        obtain ⟨rfl, rfl⟩ := ht
        exact Or.inl ⟨hb, rfl, rfl⟩
      · simp only [Test.value, hb, decide_false, Bool.cond_false, Reads] at ht
        exact Or.inr ⟨Nat.pos_of_ne_zero hb, by simpa using ht⟩
    case run =>
      obtain ⟨i, rfl, rfl, rfl⟩ := hc
      by_cases hi : u (work i) = 0
      · simp [Test.value, hi, Reads] at ht
      · simp only [Test.value, hi, decide_false, Bool.cond_false, Reads] at ht
        obtain ⟨hz, rfl, hpos, ha, hb⟩ := ht
        subst hz
        exact ⟨0, .ret _ i, rfl, hpos, ha, hb⟩
    case reject =>
      obtain ⟨rfl, rfl, rfl⟩ := hc
      simp [Test.value, Reads] at ht
    case leftTest i =>
      obtain ⟨rfl, rfl, rfl⟩ := hc
      by_cases h0 : u inA = 0
      · simp only [Test.value, h0, decide_true, Bool.cond_true, Reads] at ht
        obtain ⟨hz, rfl, hpos, hb⟩ := ht
        exact ⟨hz, rfl, hpos, h0, hb⟩
      · simp [Test.value, h0, Reads] at ht
    case rightTest i =>
      obtain ⟨rfl, rfl, rfl⟩ := hc
      by_cases h0 : u inB = 0
      · simp only [Test.value, h0, decide_true, Bool.cond_true, Reads] at ht
        obtain ⟨hz, rfl⟩ := ht
        exact ⟨hz, rfl, h0⟩
      · simp [Test.value, h0, Reads] at ht

lemma trace_reads {w c k z} {s t : State w} (h : Trace (lines w) s c t) (ht : Reads t k z) :
    Reads s (c+k) z := by
  induction h with
  | refl => simpa using ht
  | cons hs _ ih => simpa [Nat.add_assoc] using step_reads hs (ih ht)

lemma halt_reads {w} {l : Label w} {u : Fin (2+w) → ℕ} {t : Term (2+w)} {z : ℕ}
    (hl : lines w l = .halt t) (hv : t.value u = some z) : Reads (l, u) t.calls z := by
  cases l <;> simp only [lines, Line.halt.injEq, reduceCtorEq] at hl <;> subst hl <;>
    simp only [Term.value, Option.some.injEq] at hv <;> simp [Reads, Term.calls, hv]

/-- Verification of a candidate in work register `j` with value `z`: two remainder calls. -/
lemma verify_trace {w a b z} (u : Fin (2+w) → ℕ) (j : Fin w) (hj : u (work j) = z)
    (hz : 0 < z) (ha : u inA = a) (hb : u inB = b) (haz : a%z=0) (hbz : b%z=0) :
    ∃ v, Trace (lines w) (.run, u) 2 (.done j, v) ∧ v (work j) = z := by
  subst hj ha hb
  have hne : u (work j) ≠ 0 := hz.ne'
  let u₁ := Function.update u inA (u inA % u (work j))
  let u₂ := Function.update u₁ inB (u inB % u (work j))
  have h₁ : u₁ (work j) = u (work j) := Function.update_of_ne (work_ne_inA j) _ _
  have h₂ : u₂ (work j) = u (work j) := by
    simp [u₂, Function.update_of_ne (work_ne_inB j), h₁]
  have hA : u₁ inA = 0 := by simp [u₁, haz]
  have hB : u₁ inB = u inB := Function.update_of_ne inA_ne_inB.symm _ _
  have hB₂ : u₂ inB = 0 := by simp [u₂, hbz]
  have s₀ : Step (lines w) (.run, u) 0 (.left j, u) := by
    have h := Step.branch (P := lines w) (u := u) (l := .run) (cs := mainCmds w)
      (t := .eq0 (work j)) (l' := .reject) (l'' := .left j) rfl
      (by simp [mainCmds])
    simpa [Test.value, hne] using h
  have s₁ : Step (lines w) (.left j, u) 1 (.leftTest j, u₁) := by
    have h := Step.assign (P := lines w) (u := u) (l := .left j) (i := inA)
      (t := .rem inA (work j)) (l' := .leftTest j) (v := u inA % u (work j)) rfl
      (List.mem_singleton_self _) (by simp [Term.value, hne])
    simpa [Term.calls] using h
  have s₂ : Step (lines w) (.leftTest j, u₁) 0 (.right j, u₁) := by
    have h := Step.branch (P := lines w) (u := u₁) (l := .leftTest j)
      (t := .eq0 inA) (l' := .right j) (l'' := .reject) rfl (List.mem_singleton_self _)
    simpa [Test.value, hA] using h
  have s₃ : Step (lines w) (.right j, u₁) 1 (.rightTest j, u₂) := by
    have h := Step.assign (P := lines w) (u := u₁) (l := .right j) (i := inB)
      (t := .rem inB (work j)) (l' := .rightTest j) (v := u inB % u (work j)) rfl
      (List.mem_singleton_self _) (by simp [Term.value, h₁, hB, hne])
    simpa [Term.calls] using h
  have s₄ : Step (lines w) (.rightTest j, u₂) 0 (.done j, u₂) := by
    have h := Step.branch (P := lines w) (u := u₂) (l := .rightTest j)
      (t := .eq0 inB) (l' := .done j) (l'' := .reject) rfl (List.mem_singleton_self _)
    simpa [Test.value, hB₂] using h
  exact ⟨u₂, .cons s₀ (.cons s₁ (.cons s₂ (.cons s₃ (.cons s₄ (.refl _))))), h₂⟩

/-- A physical register for a write to the logical register `d` under the relabelling
`σ`: no other logical register is stored there. If `σ d` is shared, `σ` is not
injective, hence not surjective, and some work register is unused. -/
lemma exists_target {w} (σ : Fin w → Fin w) (d : Fin w) :
    ∃ p, ∀ k, k ≠ d → σ k ≠ p := by
  by_cases hs : ∀ k, k ≠ d → σ k ≠ σ d
  · exact ⟨σ d, hs⟩
  · push Not at hs
    obtain ⟨k, hkd, hk⟩ := hs
    have hni : ¬ Function.Injective σ := fun hi => hkd (hi hk)
    have hns : ¬ Function.Surjective σ :=
      fun hsur => hni (Finite.injective_iff_surjective.mpr hsur)
    obtain ⟨p, hp⟩ : ∃ p, ∀ k, σ k ≠ p := by
      simpa [Function.Surjective] using hns
    exact ⟨p, fun k _ => hp k⟩

/-- A generator run, with logical register `k` held in work register `σ k`, is replayed by
the register program with the same remainder calls. Routing changes only `σ`; each
remainder is written to a work register given by `exists_target`. -/
lemma run_trace_relabel {w a b n z} {r : Registers w} (h : Run r n z)
    (hz : 0 < z) (ha : a%z=0) (hb : b%z=0) :
    ∀ (σ : Fin w → Fin w) (u : Fin (2+w) → ℕ), u inA = a → u inB = b → r = (u ∘ work) ∘ σ →
      ∃ v j, Trace (lines w) (.run, u) (n+2) (.done j, v) ∧ v (work j) = z := by
  induction h with
  | ret r i =>
      intro σ u hA hB hru
      obtain ⟨v, hv, hvz⟩ := verify_trace u (σ i) (by rw [hru]; rfl) hz hA hB ha hb
      exact ⟨v, σ i, by simpa using hv, hvz⟩
  | mod i j d hp h ih =>
      rename_i r n' z'
      intro σ u hA hB hru
      obtain ⟨p, hp'⟩ := exists_target σ d
      have huj : u (work (σ j)) = r j := by rw [hru]; rfl
      have hui : u (work (σ i)) = r i := by rw [hru]; rfl
      let u' := Function.update u (work p) (u (work (σ i)) % u (work (σ j)))
      have hnew : Function.update r d (r i % r j) = (u' ∘ work) ∘ Function.update σ d p := by
        funext k
        simp only [u', Function.comp]
        by_cases hk : k = d
        · subst k; simp [hui, huj]
        · have hne : σ k ≠ p := hp' k hk
          simp [Function.update_of_ne hk, Function.update_of_ne (work_injective.ne hne), hru]
      obtain ⟨v, j', ht, hv⟩ := ih hz ha hb (Function.update σ d p) u'
        (by simp [u', Function.update_of_ne (work_ne_inA p).symm, hA])
        (by simp [u', Function.update_of_ne (work_ne_inB p).symm, hB]) hnew
      refine ⟨v, j', ?_, hv⟩
      have hs : Step (lines w) (.run, u) 1 (.run, u') := by
        have h := Step.assign (P := lines w) (u := u) (l := .run) (cs := mainCmds w)
          (i := work p) (t := .rem (work (σ i)) (work (σ j))) (l' := .run)
          (v := u (work (σ i)) % u (work (σ j))) rfl (by simp [mainCmds])
          (by simp [Term.value, huj, hp.ne'])
        simpa [Term.calls] using h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons hs ht
  | route f h ih =>
      intro σ u hA hB hru
      exact ih hz ha hb (σ ∘ f) u hA hB (by rw [hru]; rfl)

/-- Exact-cost equivalence with the stack-free generator and its verifier. -/
theorem executes_iff (w a b c z : ℕ) : Executes w a b c z ↔ Accepts w a b c z := by
  have hA : init w a b inA = a := by simp [init, inA]
  have hB : init w a b inB = b := by simp [init, inB]
  rw [Executes, program, ofLabels_returns]
  constructor
  · rintro ⟨l, u, t, c', ht, hl, hv, rfl⟩
    have h := trace_reads ht (halt_reads hl hv)
    simp only [Reads, hA, hB, init_work] at h
    rcases h with ⟨rfl, hc, rfl⟩ | ⟨hb, n, hn, hc, hz, ha, hbz⟩
    · rw [hc]; exact .zero _
    · rw [hc]; exact .checked hb hn hz ha hbz
  · intro h
    cases h with
    | zero =>
        have s₀ : Step (lines w) (.head, init w a 0) 0 (.ret, init w a 0) := by
          have h := Step.branch (P := lines w) (u := init w a 0) (l := .head)
            (t := .eq0 inB) (l' := .ret) (l'' := .run) rfl (List.mem_singleton_self _)
          simpa [Test.value, init, inB] using h
        exact ⟨.ret, init w a 0, .reg inA, 0, by simpa using Trace.cons s₀ (.refl _), rfl,
          by simp [Term.value, init, inA], by simp [Term.calls]⟩
    | checked hb hr hz ha hbmod =>
        rename_i n
        have s₀ : Step (lines w) (.head, init w a b) 0 (.run, init w a b) := by
          have h := Step.branch (P := lines w) (u := init w a b) (l := .head)
            (t := .eq0 inB) (l' := .ret) (l'' := .run) rfl (List.mem_singleton_self _)
          simpa [Test.value, hB, hb.ne'] using h
        obtain ⟨v, j, ht, hv⟩ := run_trace_relabel hr hz ha hbmod id (init w a b) hA hB
          (by rw [init_work]; rfl)
        exact ⟨.done j, v, .reg (work j), n+2, by simpa using Trace.cons s₀ ht, rfl,
          by simp [Term.value, hv], by simp [Term.calls]⟩

theorem executes_correct {w a b c z} (h : Executes w a b c z) : z = Nat.gcd a b :=
  ((executes_iff _ _ _ _ _).mp h).correct

theorem executes_total {w} (hw : 2 ≤ w) (a b : ℕ) :
    ∃ c, Executes w a b c (Nat.gcd a b) := by
  obtain ⟨c,hc⟩ := exists_accepts hw a b
  exact ⟨c,(executes_iff _ _ _ _ _).mpr hc⟩

/-- Every requested coefficient is achieved by one fixed register program with
`4^p+7` registers. No numerical constants or size tests are supplied to the program. -/
theorem arbitrarily_small_coefficient {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℕ, 0 < p ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ a b : ℕ, 1 ≤ b → b ≤ a →
      ∃ c, Executes (Fixed.width p) a b c (Nat.gcd a b) ∧
        (c:ℝ) ≤ ε*Real.logb 2 a+B := by
  obtain ⟨p,hp,B,hB,h⟩ := Fixed.arbitrarily_small_coefficient hε
  exact ⟨p,hp,B,hB,fun a b hb hab => by
    obtain ⟨c,hc,hbound⟩ := h a b hb hab
    exact ⟨c,(executes_iff _ _ _ _ _).mpr hc,hbound⟩⟩

end ShortGCD.TailSource
