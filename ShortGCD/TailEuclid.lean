module

public import ShortGCD.TailProgram

@[expose] public section

/-! # Flat execution inside selected register slots

`Run.lift` preserves all slots outside an injective embedding. In particular,
`euclid_inplace` computes a gcd in two slots while retaining other data.
All routing maps used by the proof name fixed source alternatives.
-/
namespace ShortGCD.TailProgram

lemma Exec.copy {w} (r : Registers w) (d i : Fin w) :
    Exec r 0 (Function.update r d (r i)) := by
  convert Exec.route r (fun j => if j = d then i else j) using 1
  funext j
  by_cases hj : j = d <;> simp [hj]

/-- A flat computation can use selected slots while all other registers survive.
No saved caller or nested-computation rule is used in this simulation. -/
theorem Run.lift {v w c z} {s : Registers v} (h : Run s c z)
    (e : Fin v → Fin w) (he : Function.Injective e) :
    ∀ r : Registers w, (∀ i, r (e i) = s i) →
      ∃ t i, Exec r c t ∧ t (e i) = z ∧
        ∀ k, (∀ j, e j ≠ k) → t k = r k := by
  classical
  induction h with
  | ret s i =>
      intro r hr
      exact ⟨r,i,.refl r,hr i,fun _ _ => rfl⟩
  | @mod s i j d hp c z h ih =>
      intro r hr
      let r' := Function.update r (e d) (r (e i) % r (e j))
      have hag : ∀ k, r' (e k) = Function.update s d (s i % s j) k := by
        intro k
        by_cases hk : k = d
        · subst k; simp [r',hr]
        · have hkd : e k ≠ e d := fun hh => hk (he hh)
          simp [r',hk,hkd,hr]
      obtain ⟨t,k,ht,hz,hframe⟩ := ih r' hag
      refine ⟨t,k,?_,hz,?_⟩
      · simpa [Nat.add_comm] using (Exec.mod r (e i) (e j) (e d) (by simpa [hr] using hp)).trans ht
      · intro l hl
        rw [hframe l hl]
        exact Function.update_of_ne (Ne.symm (hl d)) _ _
  | @route s f c z h ih =>
      intro r hr
      let F : Fin w → Fin w := fun k => if hk : ∃ i, e i = k then e (f (Classical.choose hk)) else k
      have hF : ∀ i, F (e i) = e (f i) := by
        intro i
        simp only [F, dite_eq_left (show ∃ j, e j = e i from ⟨i,rfl⟩)]
        congr 2
        exact he (Classical.choose_spec (show ∃ j, e j = e i from ⟨i,rfl⟩))
      obtain ⟨t,i,ht,hz,hframe⟩ := ih (r ∘ F) (fun j => by simp [hF,hr])
      refine ⟨t,i,by simpa using (Exec.route r F).trans ht,hz,?_⟩
      intro k hk
      rw [hframe k hk]
      have hn : ¬∃ j, e j = k := by simpa using hk
      simp [F,hn]

/-- Two-register Euclid can be run in place, preserving every other slot.
The final output occupies `i`; the other Euclidean slot may be discarded. -/
theorem euclid_inplace {w} (r : Registers w) (i j : Fin w) (hij : i ≠ j)
    (n : ℕ) (hi : r i ≤ 2^n) (hj : r j ≤ 2^n) :
    ∃ t, Exec r (2*n) t ∧ t i = Nat.gcd (r i) (r j) ∧
      ∀ k, k ≠ i → k ≠ j → t k = r k := by
  have hc := (computes_maxCost (w := 2) (by omega) hi hj).mono (maxCost_pow_le (by omega) n)
  obtain ⟨c,hc,hrun⟩ := hc
  let e : Fin 2 → Fin w := ![i,j]
  have hinj : Function.Injective e := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [e]
  have hag : ∀ k, r (e k) = inputs 2 (r i) (r j) k := by
    intro k; fin_cases k <;> simp [e,inputs]
  obtain ⟨t,k,ht,hz,hframe⟩ := hrun.lift e hinj r hag
  refine ⟨Function.update t i (t (e k)),?_,by simpa using hz,?_⟩
  · simpa using (ht.trans (Exec.copy t i (e k))).mono hc
  · intro l hli hlj
    rw [Function.update_of_ne hli]
    apply hframe
    intro x
    fin_cases x
    · simpa [e] using Ne.symm hli
    · simpa [e] using Ne.symm hlj

end ShortGCD.TailProgram
