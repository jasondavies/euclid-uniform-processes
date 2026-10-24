module

public import ShortGCD.TailAsymptotic

@[expose] public section

/-! The control flow of the register program of `TailSource`, with each verification check
taken as one compound step. `TailRecursive` is proved against this form; `TailSource` writes
the same program in the book's syntax, and both are equivalent to `TailProgram.Accepts` at
exact cost (`executes_iff`, `TailSource.executes_iff`).

The numeric state is the `w` work registers; the inputs `a, b` are parameters of `Step`.
The generator `TailProgram.Run` also has a cost-free `route` step that relabels all
registers at once. `run_trace_relabel` replays a routed run on the physical registers by
tracking the relabelling in the proof.
-/
namespace ShortGCD.TailFlow
open TailProgram

inductive Control (w : ℕ) where
  | run
  | left (i : Fin w)
  | right (i : Fin w)
  | done (i : Fin w)
  | reject
  deriving DecidableEq, Fintype

/-- The control line and the work registers. In this form the checks read `a` and `b`
without storing results, so the inputs are the parameters `a b` of `Step`; `TailSource`'s
verification overwrites `u₀, u₁`. The total numeric storage is `w+2` registers. -/
abbrev State (w : ℕ) := Control w × Registers w

/-- The commands of the control flow, read on the inputs `a b`. At line `run`
the program may assign a remainder of two registers to any work register, or pass
to the verification of a candidate. A zero candidate and a failed check loop. -/
inductive Step (a b : ℕ) : {w : ℕ} → State w → ℕ → State w → Prop
  | rem {w} (r : Registers w) (i j d : Fin w) (hp : 0 < r j) :
      Step a b (.run,r) 1 (.run,Function.update r d (r i % r j))
  | choose {w} (r : Registers w) (i : Fin w) (hp : 0 < r i) :
      Step a b (.run,r) 0 (.left i,r)
  | zero {w} (r : Registers w) (i : Fin w) (hz : r i = 0) :
      Step a b (.run,r) 0 (.reject,r)
  | left_ok {w} (r : Registers w) (i : Fin w) (hp : 0 < r i) (h : a % r i = 0) :
      Step a b (.left i,r) 1 (.right i,r)
  | left_bad {w} (r : Registers w) (i : Fin w) (hp : 0 < r i) (h : a % r i ≠ 0) :
      Step a b (.left i,r) 1 (.reject,r)
  | right_ok {w} (r : Registers w) (i : Fin w) (hp : 0 < r i) (h : b % r i = 0) :
      Step a b (.right i,r) 1 (.done i,r)
  | right_bad {w} (r : Registers w) (i : Fin w) (hp : 0 < r i) (h : b % r i ≠ 0) :
      Step a b (.right i,r) 1 (.reject,r)
  | loop {w} (r : Registers w) : Step a b (.reject,r) 0 (.reject,r)

inductive Trace (a b : ℕ) {w : ℕ} : State w → ℕ → State w → Prop
  | refl (s) : Trace a b s 0 s
  | cons {s t u c k} (hs : Step a b s c t) (ht : Trace a b t k u) :
      Trace a b s (c+k) u

/-- Backward assertion used to extract a generator run from a machine trace. -/
def Returns {w} (a b : ℕ) (s : State w) (c z : ℕ) : Prop :=
  match s.1 with
  | .run => ∃ n, Run s.2 n z ∧ c=n+2 ∧ 0 < z ∧ a%z=0 ∧ b%z=0
  | .left i => z=s.2 i ∧ c=2 ∧ 0 < z ∧ a%z=0 ∧ b%z=0
  | .right i => z=s.2 i ∧ c=1 ∧ 0 < z ∧ b%z=0
  | .done i => z=s.2 i ∧ c=0
  | .reject => False

lemma Step.returns {w a b c k z} {s t : State w} (h : Step a b s c t)
    (ht : Returns a b t k z) : Returns a b s (c+k) z := by
  cases h with
  | rem r i j d hp =>
      obtain ⟨n,hn,hk,hz,ha,hb⟩ := ht
      exact ⟨n+1,.mod i j d hp hn,by omega,hz,ha,hb⟩
  | choose r i hp =>
      obtain ⟨rfl,rfl,hz,ha,hb⟩ := ht
      exact ⟨0,.ret r i,rfl,hz,ha,hb⟩
  | zero => exact False.elim ht
  | left_ok r i hp ha =>
      obtain ⟨rfl,rfl,hz,hb⟩ := ht
      exact ⟨rfl,rfl,hz,ha,hb⟩
  | left_bad => exact False.elim ht
  | right_ok r i hp hb =>
      obtain ⟨rfl,rfl⟩ := ht
      exact ⟨rfl,rfl,hp,hb⟩
  | right_bad => exact False.elim ht
  | loop => exact False.elim ht

lemma Trace.returns {w a b c k z} {s t : State w} (h : Trace a b s c t)
    (ht : Returns a b t k z) : Returns a b s (c+k) z := by
  induction h with
  | refl => simpa using ht
  | cons hs ht' ih => simpa [Nat.add_assoc] using hs.returns (ih ht)

/-- A physical register for a write to the logical register `d` under the relabelling
`σ`: no other logical register is stored there. If `σ d` is shared, `σ` is not
injective, hence not surjective, and some physical register is unused. -/
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

/-- A generator run, with logical register `k` held in physical register `σ k`, is
replayed by the control flow with the same remainder calls. Routing changes only
`σ`; each remainder is written to a physical register given by `exists_target`. -/
lemma run_trace_relabel {w a b n z} {r : Registers w} (h : Run r n z)
    (hz : 0 < z) (ha : a%z=0) (hb : b%z=0) :
    ∀ (σ : Fin w → Fin w) (q : Registers w), r = q ∘ σ →
      ∃ t i, Trace a b (.run,q) (n+2) (.done i,t) ∧ t i=z := by
  induction h with
  | ret r i =>
      intro σ q hrq
      have hi : q (σ i) = r i := by rw [hrq]; rfl
      refine ⟨q, σ i, ?_, hi⟩
      exact .cons (.choose q (σ i) (hi ▸ hz)) (.cons (.left_ok q (σ i) (hi ▸ hz) (hi ▸ ha))
        (.cons (.right_ok q (σ i) (hi ▸ hz) (hi ▸ hb)) (.refl _)))
  | mod i j d hp h ih =>
      rename_i r n' z'
      intro σ q hrq
      obtain ⟨p, hp'⟩ := exists_target σ d
      have hqj : q (σ j) = r j := by rw [hrq]; rfl
      have hqi : q (σ i) = r i := by rw [hrq]; rfl
      have hnew : Function.update r d (r i % r j) =
          Function.update q p (q (σ i) % q (σ j)) ∘ Function.update σ d p := by
        funext k
        by_cases hk : k = d
        · subst k; simp [hqi, hqj]
        · have hne : σ k ≠ p := hp' k hk
          simp [Function.update_of_ne hk, Function.update_of_ne hne, hrq]
      obtain ⟨t, i', ht, hti⟩ := ih hz ha hb (Function.update σ d p) _ hnew
      refine ⟨t, i', ?_, hti⟩
      have hs := Trace.cons (.rem q (σ i) (σ j) p (hqj ▸ hp)) ht
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  | route f h ih =>
      intro σ q hrq
      exact ih hz ha hb (σ ∘ f) q (by rw [hrq]; rfl)

lemma run_trace {w a b n z} {r : Registers w} (h : Run r n z)
    (hz : 0 < z) (ha : a%z=0) (hb : b%z=0) :
    ∃ t i, Trace a b (.run,r) (n+2) (.done i,t) ∧ t i=z :=
  run_trace_relabel h hz ha hb id r rfl

/-- Head: return the first input when the second is zero; otherwise start the
control flow with the work registers holding copies of the two inputs. -/
def Executes (w a b c z : ℕ) : Prop :=
  (b=0 ∧ c=0 ∧ z=a) ∨
  (0 < b ∧ ∃ r i, Trace a b (.run,inputs w a b) c (.done i,r) ∧ r i=z)

/-- Exact-cost equivalence with the stack-free generator and its verifier. -/
theorem executes_iff (w a b c z : ℕ) : Executes w a b c z ↔ Accepts w a b c z := by
  constructor
  · rintro (⟨rfl,rfl,rfl⟩ | ⟨hb,r,i,ht,hz⟩)
    · exact .zero _
    · have h := ht.returns (k := 0) (z := z) (show Returns a b (.done i,r) 0 z from ⟨hz.symm,rfl⟩)
      obtain ⟨n,hn,hc,hp,ha,hbz⟩ := h
      have hc' : c=n+2 := by omega
      rw [hc']
      exact .checked hb hn hp ha hbz
  · intro h
    cases h with
    | zero => exact Or.inl ⟨rfl,rfl,rfl⟩
    | checked hb hr hz ha hbmod =>
        obtain ⟨r,i,ht,hi⟩ := run_trace hr hz ha hbmod
        exact Or.inr ⟨hb,r,i,ht,hi⟩

end ShortGCD.TailFlow
