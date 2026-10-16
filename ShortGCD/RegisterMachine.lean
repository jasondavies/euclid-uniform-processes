import ShortGCD.RegisterProgram
import ShortGCD.Euclid

namespace ShortGCD.RegisterProgram

def Computes {w : ℕ} (r : Registers w) (K z : ℕ) : Prop :=
  ∃ n, n ≤ K ∧ Run r n z

theorem Computes.mono {w K L z} {r : Registers w}
    (h : Computes r K z) (hKL : K ≤ L) : Computes r L z := by
  obtain ⟨n, hn, hr⟩ := h
  exact ⟨n, hn.trans hKL, hr⟩

theorem Computes.ret {w K} (r : Registers w) (i : Fin w) : Computes r K (r i) :=
  ⟨0, Nat.zero_le _, .ret r i⟩

theorem Computes.route {w K z} {r : Registers w} (f : Fin w → Fin w)
    (h : Computes (r ∘ f) K z) : Computes r K z := by
  obtain ⟨n, hn, hr⟩ := h
  exact ⟨n, hn, .route f hr⟩

theorem Computes.pair {w a b K z} {r : Registers w} (i j : Fin w)
    (hi : r i = a) (hj : r j = b) (h : Computes (inputs w a b) K z) :
    Computes r K z := by
  apply Computes.route (fun k => if k.val = 1 then j else i)
  convert h using 1
  funext k
  by_cases hk : k.val = 1 <;> simp [inputs, hk, hi, hj]

theorem Computes.scale {w K z g} {r : Registers w} (h : Computes r K z)
    (hg : 0 < g) : Computes (fun i => g*r i) K (g*z) := by
  obtain ⟨n, hn, hr⟩ := h
  exact ⟨n, hn, hr.scale hg⟩

/-- Finite state transitions, interpreted by the same generator equations.
The cost is an upper bound; no padding instructions are required. -/
inductive Exec {w : ℕ} : Registers w → ℕ → Registers w → Prop
  | refl (r) : Exec r 0 r
  | mod (r) (i j d : Fin w) (hp : 0 < r j) :
      Exec r 1 (Function.update r d (r i % r j))
  | route (r) (f : Fin w → Fin w) : Exec r 0 (r ∘ f)
  | sub {r K z} (d : Fin w) : Computes r K z → Exec r K (Function.update r d z)
  | trans {r s t K L} : Exec r K s → Exec s L t → Exec r (K+L) t
  | mono {r s K L} : Exec r K s → K ≤ L → Exec r L s

theorem Exec.then_compute {w K L z} {r s : Registers w}
    (h : Exec r K s) (hc : Computes s L z) : Computes r (K+L) z := by
  induction h generalizing L with
  | refl => simpa using hc
  | mod r i j d hp =>
      obtain ⟨n, hn, hr⟩ := hc
      exact ⟨n+1, by omega, .mod i j d hp hr⟩
  | route r f => simpa using hc.route f
  | sub d hs =>
      obtain ⟨n, hn, hr⟩ := hs
      obtain ⟨m, hm, hs⟩ := hc
      exact ⟨n+m, by omega, .sub d hr hs⟩
  | trans h₁ h₂ ih₁ ih₂ =>
      simpa [Nat.add_assoc] using ih₁ (ih₂ hc)
  | mono h hKL ih => exact (ih hc).mono (by omega)

theorem Exec.finish {w K} {r s : Registers w} (h : Exec r K s) (i : Fin w) :
    Computes r K (s i) := by
  simpa using h.then_compute (Computes.ret (K := 0) s i)

/-- A finite width-dependent minimum over successful generator computations. -/
noncomputable def cost (w a b : ℕ) : ℕ := by
  classical
  exact if hw : 2 ≤ w then Nat.find (exists_run_gcd hw a b) else 0

theorem computes_cost {w} (hw : 2 ≤ w) (a b : ℕ) :
    Computes (inputs w a b) (cost w a b) (Nat.gcd a b) := by
  classical
  simp only [cost, dite_eq_left hw]
  exact ⟨_, le_rfl, Nat.find_spec (exists_run_gcd hw a b)⟩

theorem cost_le {w a b K} (hw : 2 ≤ w)
    (h : Computes (inputs w a b) K (Nat.gcd a b)) : cost w a b ≤ K := by
  obtain ⟨n, hn, hr⟩ := h
  classical
  simp only [cost, dite_eq_left hw]
  exact (Nat.find_min' (exists_run_gcd hw a b) hr).trans hn

noncomputable def maxCost (w A : ℕ) : ℕ :=
  (Finset.range (A+1)).sup (fun a => (Finset.range (A+1)).sup (cost w a))

theorem cost_le_maxCost {w a b A} (ha : a ≤ A) (hb : b ≤ A) :
    cost w a b ≤ maxCost w A :=
  Finset.le_sup_of_le (Finset.mem_range.mpr (by omega))
    (Finset.le_sup (Finset.mem_range.mpr (by omega)))

theorem computes_maxCost {w a b A} (hw : 2 ≤ w) (ha : a ≤ A) (hb : b ≤ A) :
    Computes (inputs w a b) (maxCost w A) (Nat.gcd a b) :=
  (computes_cost hw a b).mono (cost_le_maxCost ha hb)

theorem maxCost_le {w A K} (hw : 2 ≤ w)
    (h : ∀ a b, a ≤ A → b ≤ A → Computes (inputs w a b) K (Nat.gcd a b)) :
    maxCost w A ≤ K := by
  apply Finset.sup_le
  intro a ha
  apply Finset.sup_le
  intro b hb
  exact cost_le hw (h a b (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp ha))
    (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hb)))

end ShortGCD.RegisterProgram
