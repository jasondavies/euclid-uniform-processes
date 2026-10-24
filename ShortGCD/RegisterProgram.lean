module

public import Mathlib

@[expose] public section

/-! # Register programs

Finite register programs in the sense of Moschovakis, *Abstract Recursion and Intrinsic
Complexity* (2019), §2F, over the vocabulary `{rem, eq0}`, with the finite nondeterminism of
§2E. A program with `k` registers `u₀, …, u_{k-1}` is a sequence of lines numbered
`0, …, L`. A line is either a halting command `halt, return t`, or a list of commands any one
of which may be taken: an assignment `uᵢ := t, goto l` or a branching
`if t then goto l else goto l'`. The terms are the book's prime terms (§2F, primitive
register programs): `uᵢ` and `rem(uᵢ, uⱼ)` of sort `ind`, and `tt`, `ff` and `eq0(uᵢ)` of
sort `boole`.

The states are pairs of a line and the register values. As in the book's iterator, an
assignment updates one register and a branching moves to the line selected by its test. The
remainder is partial, as in the book's structures: `rem(x, 0)` is undefined, so an assignment
of it has no transition. A computation starts at line `0`, and it converges when it reaches a
halting line, returning the value of its term. Its cost is the number of remainder
evaluations, as in the book's (2E-5).

`ofLabels` numbers the lines of a program written with labels from a finite type, putting
the start line at `0`; `ofLabels_returns` shows that numbering changes no computation.
-/

namespace ShortGCD.Register

/-- Prime terms of sort `ind` in the registers `u₀, …, u_{k-1}`. -/
inductive Term (k : ℕ) where
  | reg (i : Fin k)
  | rem (i j : Fin k)

/-- Prime terms of sort `boole`. -/
inductive Test (k : ℕ) where
  | tt
  | ff
  | eq0 (i : Fin k)

/-- A non-halting command, jumping to lines in `ι`. -/
inductive Cmd (k : ℕ) (ι : Type) where
  | assign (i : Fin k) (t : Term k) (l : ι)
  | branch (t : Test k) (l l' : ι)

/-- A line: a halting command, or a list of alternative commands. -/
inductive Line (k : ℕ) (ι : Type) where
  | halt (t : Term k)
  | cmds (cs : List (Cmd k ι))

/-- A register program with `k` registers: lines numbered `0, …, L`. -/
structure Program (k : ℕ) where
  L : ℕ
  line : Fin (L+1) → Line k (Fin (L+1))

variable {k : ℕ} {ι κ : Type}

/-- The value of a term, undefined for a remainder with divisor `0`. -/
def Term.value : Term k → (Fin k → ℕ) → Option ℕ
  | .reg i, u => some (u i)
  | .rem i j, u => if u j = 0 then none else some (u i % u j)

/-- The number of remainder calls made in evaluating a term. -/
def Term.calls : Term k → ℕ
  | .reg _ => 0
  | .rem _ _ => 1

/-- The value of a test. -/
def Test.value : Test k → (Fin k → ℕ) → Bool
  | .tt, _ => true
  | .ff, _ => false
  | .eq0 i, u => decide (u i = 0)

/-- One transition, with its remainder cost, of the program whose lines are `P`. -/
inductive Step (P : ι → Line k ι) : ι × (Fin k → ℕ) → ℕ → ι × (Fin k → ℕ) → Prop
  | assign {l : ι} {u : Fin k → ℕ} {cs i t l' v} (hl : P l = .cmds cs)
      (hc : Cmd.assign i t l' ∈ cs) (hv : t.value u = some v) :
      Step P (l, u) t.calls (l', Function.update u i v)
  | branch {l : ι} {u : Fin k → ℕ} {cs t l' l''} (hl : P l = .cmds cs)
      (hc : Cmd.branch t l' l'' ∈ cs) :
      Step P (l, u) 0 (cond (t.value u) l' l'', u)

/-- Finite computations, with their total remainder cost. -/
inductive Trace (P : ι → Line k ι) : ι × (Fin k → ℕ) → ℕ → ι × (Fin k → ℕ) → Prop
  | refl (s) : Trace P s 0 s
  | cons {s t u c c'} (hs : Step P s c t) (ht : Trace P t c' u) : Trace P s (c+c') u

/-- From state `s`, some convergent computation returns `z` with `c` remainder calls. -/
def Halts (P : ι → Line k ι) (s : ι × (Fin k → ℕ)) (c z : ℕ) : Prop :=
  ∃ l u t c', Trace P s c' (l, u) ∧ P l = .halt t ∧ t.value u = some z ∧ c = c'+t.calls

/-- Started at line `0` with registers `x`, some convergent computation of `P` returns `z`
with `c` remainder calls. -/
def Program.Returns (P : Program k) (x : Fin k → ℕ) (c z : ℕ) : Prop :=
  Halts P.line (0, x) c z

/-! ## Numbering the lines -/

/-- Rename the lines a command jumps to. -/
def Cmd.map (e : ι → κ) : Cmd k ι → Cmd k κ
  | .assign i t l => .assign i t (e l)
  | .branch t l l' => .branch t (e l) (e l')

/-- Rename the lines of a line's commands. -/
def Line.map (e : ι → κ) : Line k ι → Line k κ
  | .halt t => .halt t
  | .cmds cs => .cmds (cs.map (Cmd.map e))

/-- A numbering of a finite type of labels with `s` at `0`. -/
noncomputable def numbering [Fintype ι] (s : ι) : ι ≃ Fin (Fintype.card ι - 1 + 1) :=
  have h : Fintype.card ι = Fintype.card ι - 1 + 1 :=
    (Nat.sub_one_add_one (Fintype.card_pos_iff.mpr ⟨s⟩).ne').symm
  let e := Fintype.equivFinOfCardEq h
  e.trans (Equiv.swap (e s) 0)

lemma numbering_start [Fintype ι] (s : ι) : numbering s s = 0 := by
  simp [numbering]

/-- The program whose lines are `P`, numbered with the start line `s` at `0`. -/
noncomputable def ofLabels [Fintype ι] (P : ι → Line k ι) (s : ι) : Program k where
  L := Fintype.card ι - 1
  line m := (P ((numbering s).symm m)).map (numbering s)

section relabel

variable (P : ι → Line k ι) (e : ι ≃ κ)

/-- The program `P` with its lines renamed along `e`. -/
def relabel : κ → Line k κ := fun m => (P (e.symm m)).map e

lemma step_relabel {s t : ι × (Fin k → ℕ)} {c} (h : Step P s c t) :
    Step (relabel P e) (e s.1, s.2) c (e t.1, t.2) := by
  cases h with
  | assign hl hc hv =>
    exact .assign (by simp [relabel, hl, Line.map])
      (List.mem_map_of_mem (f := Cmd.map e) hc) hv
  | @branch l u cs t l' l'' hl hc =>
    have h := Step.branch (P := relabel P e) (u := u) (l := e l) (t := t)
      (by simp [relabel, hl, Line.map]) (List.mem_map_of_mem (f := Cmd.map e) hc)
    cases ht : t.value u <;> simpa [ht] using h

lemma step_unrelabel {m m' : κ} {u u' : Fin k → ℕ} {c}
    (h : Step (relabel P e) (m, u) c (m', u')) :
    Step P (e.symm m, u) c (e.symm m', u') := by
  cases h with
  | @assign _ _ cs' i t l' v hl hc hv =>
    cases hP : P (e.symm m) with
    | halt => simp [relabel, hP, Line.map] at hl
    | cmds cs =>
      simp only [relabel, hP, Line.map, Line.cmds.injEq] at hl
      subst hl
      obtain ⟨cmd, hcmd, hmap⟩ := List.mem_map.mp hc
      cases cmd with
      | assign i₀ t₀ l₀ =>
        simp only [Cmd.map, Cmd.assign.injEq] at hmap
        obtain ⟨rfl, rfl, rfl⟩ := hmap
        simpa using Step.assign (P := P) hP hcmd hv
      | branch => simp [Cmd.map] at hmap
  | @branch _ _ cs' t l' l'' hl hc =>
    cases hP : P (e.symm m) with
    | halt => simp [relabel, hP, Line.map] at hl
    | cmds cs =>
      simp only [relabel, hP, Line.map, Line.cmds.injEq] at hl
      subst hl
      obtain ⟨cmd, hcmd, hmap⟩ := List.mem_map.mp hc
      cases cmd with
      | assign => simp [Cmd.map] at hmap
      | branch t₀ l₀ l₀' =>
        simp only [Cmd.map, Cmd.branch.injEq] at hmap
        obtain ⟨rfl, rfl, rfl⟩ := hmap
        have h := Step.branch (P := P) (u := u) hP hcmd
        cases ht : t₀.value u <;> simpa [ht] using h

lemma trace_relabel {s t : ι × (Fin k → ℕ)} {c} (h : Trace P s c t) :
    Trace (relabel P e) (e s.1, s.2) c (e t.1, t.2) := by
  induction h with
  | refl => exact .refl _
  | cons hs _ ih => exact .cons (step_relabel P e hs) ih

lemma trace_unrelabel {s t : κ × (Fin k → ℕ)} {c} (h : Trace (relabel P e) s c t) :
    Trace P (e.symm s.1, s.2) c (e.symm t.1, t.2) := by
  induction h with
  | refl => exact .refl _
  | cons hs _ ih => exact .cons (step_unrelabel P e hs) ih

lemma halts_relabel (l : ι) (u : Fin k → ℕ) (c z : ℕ) :
    Halts (relabel P e) (e l, u) c z ↔ Halts P (l, u) c z := by
  constructor
  · rintro ⟨m, v, t, c', ht, hl, hv, rfl⟩
    have h := trace_unrelabel P e ht
    simp only [Equiv.symm_apply_apply] at h
    refine ⟨e.symm m, v, t, c', h, ?_, hv, rfl⟩
    cases hP : P (e.symm m) <;> simp_all [relabel, Line.map]
  · rintro ⟨l', v, t, c', ht, hl, hv, rfl⟩
    refine ⟨e l', v, t, c', trace_relabel P e ht, by simp [relabel, hl, Line.map], hv, rfl⟩

end relabel

/-- Numbering the lines changes no computation. -/
theorem ofLabels_returns [Fintype ι] (P : ι → Line k ι) (s : ι) (x : Fin k → ℕ) (c z : ℕ) :
    (ofLabels P s).Returns x c z ↔ Halts P (s, x) c z := by
  have h := halts_relabel P (numbering s) s x c z
  rw [numbering_start] at h
  exact h

end ShortGCD.Register
