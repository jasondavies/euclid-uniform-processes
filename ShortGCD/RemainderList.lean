module

public import ShortGCD.CoprimeCertificate

@[expose] public section

/-!
# Remainder derivations

A *remainder derivation* from `a, b` is a list `r₁, …, r_k` in which each `rᵢ = x % y` for
some `x, y ≠ 0` among `a, b, r₁, …, r_{i-1}`. `D a b` is the length of a shortest derivation
containing `1` (`0` if `1` is an input, and `0` by the `sInf ∅ = 0` convention when no
derivation exists, that is, for non-coprime pairs).

* `exists_list_iff`: a derivation of length `≤ k` reaching `1` exists iff a sound set of at
  most `k` remainder facts reaches `1`. Building a derivation from a reachability proof
  merges the derivations of the two operands and drops repeated values, so its entries are
  distinct outputs of facts.
* `callsRem_eq_D`: on coprime pairs, the intrinsic `calls(rem)`-complexity of `Nat.Coprime`
  in `Nε` equals `D`. For the book's relation, which requires positive inputs, see
  `callsCoprimeness_eq_callsRem`.
-/

namespace ShortGCD

open Finset

/-- Each entry is `x % y` for `x, y` available (the list `avail`, then earlier entries) with
`y ≠ 0`. -/
def ValidFrom : List ℕ → List ℕ → Prop
  | _, [] => True
  | avail, v :: rest =>
    (∃ x ∈ avail, ∃ y ∈ avail, y ≠ 0 ∧ v = x % y) ∧ ValidFrom (v :: avail) rest

theorem ValidFrom.mono : ∀ {avail avail' l : List ℕ}, (∀ z ∈ avail, z ∈ avail') →
    ValidFrom avail l → ValidFrom avail' l
  | _, _, [], _, _ => trivial
  | _, _, _ :: _, h, ⟨⟨x, hx, y, hy, hy0, hv⟩, hrest⟩ =>
    ⟨⟨x, h x hx, y, h y hy, hy0, hv⟩, ValidFrom.mono (fun z hz ↦ by
      rcases List.mem_cons.1 hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h z hz)) hrest⟩

theorem ValidFrom.append : ∀ {avail l₁ l₂ : List ℕ}, ValidFrom avail l₁ →
    ValidFrom (l₁.reverse ++ avail) l₂ → ValidFrom avail (l₁ ++ l₂)
  | _, [], _, _, h₂ => h₂
  | _, _ :: _, _, ⟨hv, h₁⟩, h₂ => ⟨hv, ValidFrom.append h₁ (by simpa using h₂)⟩

/-- Dropping entries that are already available keeps a derivation valid. -/
theorem ValidFrom.filter {S : List ℕ} : ∀ {avail T l : List ℕ}, (∀ z ∈ S, z ∈ T) →
    (∀ z ∈ avail, z ∈ T) → ValidFrom avail l → ValidFrom T (l.filter fun v ↦ v ∉ S)
  | _, _, [], _, _, _ => trivial
  | _, T, v :: _, hST, hT, ⟨⟨x, hx, y, hy, hy0, hv⟩, hrest⟩ => by
    by_cases hvS : v ∈ S
    · rw [List.filter_cons_of_neg (by simpa using hvS)]
      refine ValidFrom.filter hST (fun z hz ↦ ?_) hrest
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hST z hvS
      · exact hT z hz
    · rw [List.filter_cons_of_pos (by simpa using hvS)]
      refine ⟨⟨x, hT x hx, y, hT y hy, hy0, hv⟩, ValidFrom.filter (fun z hz ↦
        List.mem_cons_of_mem _ (hST z hz)) (fun z hz ↦ ?_) hrest⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hT z hz)

/-- From a reachability proof, a derivation with distinct entries, each the output of a fact,
which reaches the value. -/
theorem exists_list_of_reach {F : Finset RemFact} {a b x : ℕ} (hF : SoundRems F)
    (h : Reach F a b x) : ∃ l : List ℕ, ValidFrom [a, b] l ∧ x ∈ a :: b :: l ∧ l.Nodup ∧
      ∀ v ∈ l, ∃ f ∈ F, f.2.2 = v := by
  induction h with
  | left => exact ⟨[], trivial, by simp, List.nodup_nil, by simp⟩
  | right => exact ⟨[], trivial, by simp, List.nodup_nil, by simp⟩
  | @step x y r hf _ _ ihx ihy =>
    obtain ⟨lx, hvx, hxl, hndx, hfx⟩ := ihx
    obtain ⟨ly, hvy, hyl, hndy, hfy⟩ := ihy
    set S := a :: b :: lx
    set l₂ := ly.filter fun v ↦ v ∉ S
    have hS : ∀ z ∈ S, z ∈ lx.reverse ++ [a, b] := fun z hz ↦ by
      simp only [S, List.mem_cons] at hz; simp; tauto
    have hv₂ : ValidFrom (lx.reverse ++ [a, b]) l₂ :=
      ValidFrom.filter hS (fun z hz ↦ by simp at hz ⊢; tauto) hvy
    have hv₁₂ : ValidFrom [a, b] (lx ++ l₂) := ValidFrom.append hvx hv₂
    -- every value of `a :: b :: ly` is available after `lx ++ l₂`
    have hcover : ∀ z ∈ a :: b :: ly, z ∈ a :: b :: (lx ++ l₂) := fun z hz ↦ by
      by_cases hzS : z ∈ S
      · simp only [S, List.mem_cons] at hzS ⊢; simp; tauto
      · have : z ∈ ly := by simp only [S, List.mem_cons] at hz hzS; tauto
        simp [l₂, this, hzS]
    have hnd₁₂ : (lx ++ l₂).Nodup := by
      refine List.nodup_append.2 ⟨hndx, hndy.filter _, fun u hu v hv ↦ ?_⟩
      rintro rfl
      simp only [l₂, List.mem_filter, decide_eq_true_eq] at hv
      exact hv.2 (by simp [S, hu])
    have hf₁₂ : ∀ v ∈ lx ++ l₂, ∃ f ∈ F, f.2.2 = v := fun v hv ↦ by
      rcases List.mem_append.1 hv with hv | hv
      · exact hfx v hv
      · exact hfy v (List.mem_filter.1 hv).1
    by_cases hr : r ∈ a :: b :: (lx ++ l₂)
    · exact ⟨lx ++ l₂, hv₁₂, hr, hnd₁₂, hf₁₂⟩
    · obtain ⟨hy0, hrxy⟩ := hF _ hf
      refine ⟨lx ++ l₂ ++ [r], ValidFrom.append hv₁₂ ⟨⟨x, ?_, y, ?_, hy0, hrxy⟩, trivial⟩,
        by simp, ?_, fun v hv ↦ ?_⟩
      · have : x ∈ a :: b :: (lx ++ l₂) := by
          simp only [S, List.mem_cons] at hxl; simp; tauto
        simp only [List.mem_cons, List.mem_append, List.mem_reverse] at this ⊢; tauto
      · have : y ∈ a :: b :: (lx ++ l₂) := hcover y hyl
        simp only [List.mem_cons, List.mem_append, List.mem_reverse] at this ⊢; tauto
      · exact List.nodup_append.2 ⟨hnd₁₂, List.nodup_singleton r,
          fun u hu v hv ↦ by simp at hv; rintro rfl; exact hr (by simp [hv ▸ hu])⟩
      · rcases List.mem_append.1 hv with hv | hv
        · exact hf₁₂ v hv
        · exact ⟨_, hf, (List.mem_singleton.1 hv).symm⟩

/-- From a derivation, a set of facts (one per entry) reaching all its entries. -/
theorem exists_facts_of_validFrom {a b : ℕ} : ∀ {avail l : List ℕ} {F₀ : Finset RemFact},
    SoundRems F₀ → (∀ z ∈ avail, Reach F₀ a b z) → ValidFrom avail l →
      ∃ F, F₀ ⊆ F ∧ SoundRems F ∧ F.card ≤ F₀.card + l.length ∧ ∀ z ∈ l, Reach F a b z
  | _, [], F₀, hF₀, _, _ => ⟨F₀, subset_rfl, hF₀, by simp, by simp⟩
  | avail, v :: rest, F₀, hF₀, havail, ⟨⟨x, hx, y, hy, hy0, hv⟩, hrest⟩ => by
    classical
    set F₁ := insert (x, y, v) F₀
    have hF₁ : SoundRems F₁ := fun f hf ↦ by
      rcases mem_insert.1 hf with rfl | hf
      · exact ⟨hy0, hv⟩
      · exact hF₀ f hf
    have hvreach : Reach F₁ a b v :=
      .step (mem_insert_self _ _) ((havail x hx).mono (subset_insert _ _))
        ((havail y hy).mono (subset_insert _ _))
    obtain ⟨F, hsub, hF, hcard, hreach⟩ := exists_facts_of_validFrom hF₁ (fun z hz ↦ by
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hvreach
      · exact (havail z hz).mono (subset_insert _ _)) hrest
    refine ⟨F, (subset_insert _ _).trans hsub, hF, ?_, fun z hz ↦ ?_⟩
    · have h₁ : F₁.card ≤ F₀.card + 1 := card_insert_le _ _
      simp only [List.length_cons]
      omega
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact hvreach.mono hsub
      · exact hreach z hz

/-- A derivation of length at most `k` reaching `1` exists iff a sound set of at most `k`
remainder facts reaches `1`. -/
theorem exists_list_iff (a b k : ℕ) :
    (∃ l : List ℕ, ValidFrom [a, b] l ∧ 1 ∈ a :: b :: l ∧ l.length ≤ k) ↔
      ∃ F : Finset RemFact, SoundRems F ∧ Reach F a b 1 ∧ F.card ≤ k := by
  classical
  constructor
  · rintro ⟨l, hl, h1, hk⟩
    obtain ⟨F, -, hF, hcard, hreach⟩ := exists_facts_of_validFrom (F₀ := ∅) (a := a) (b := b)
      (fun f hf ↦ by simp at hf) (fun z hz ↦ by
        rcases List.mem_cons.1 hz with rfl | hz
        · exact .left
        · rcases List.mem_singleton.1 hz with rfl
          exact .right) hl
    have hcard' : F.card ≤ l.length := by simpa using hcard
    refine ⟨F, hF, ?_, hcard'.trans hk⟩
    rcases List.mem_cons.1 h1 with h | h1
    · exact h ▸ .left
    rcases List.mem_cons.1 h1 with h | h1
    · exact h ▸ .right
    · exact hreach 1 h1
  · rintro ⟨F, hF, h1, hk⟩
    obtain ⟨l, hl, h1l, hnd, hfacts⟩ := exists_list_of_reach hF h1
    refine ⟨l, hl, h1l, ?_⟩
    calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ ≤ (F.image fun f ↦ f.2.2).card := card_le_card fun v hv ↦ by
          obtain ⟨f, hf, rfl⟩ := hfacts v (List.mem_toFinset.1 hv)
          exact mem_image_of_mem _ hf
      _ ≤ F.card := card_image_le
      _ ≤ k := hk

/-- `D a b`: the length of a shortest remainder derivation of `1` from `a, b`. -/
noncomputable def D (a b : ℕ) : ℕ :=
  sInf {k | ∃ l : List ℕ, ValidFrom [a, b] l ∧ 1 ∈ a :: b :: l ∧ l.length = k}

theorem D_eq_derivLen (a b : ℕ) : D a b = derivLen a b := by
  apply sInf_eq_of_exists_le_iff
  intro k
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, ⟨l, hl, h1, rfl⟩, hj⟩
    obtain ⟨F, hF, h1F, hk⟩ := (exists_list_iff a b k).1 ⟨l, hl, h1, hj⟩
    exact ⟨F.card, ⟨F, hF, h1F, rfl⟩, hk⟩
  · rintro ⟨j, ⟨F, hF, h1F, rfl⟩, hj⟩
    obtain ⟨l, hl, h1, hk⟩ := (exists_list_iff a b k).2 ⟨F, hF, h1F, hj⟩
    exact ⟨l.length, ⟨l, hl, h1, rfl⟩, hk⟩

/-- **The reformulation for uniform processes.** For coprime `a, b`, the intrinsic
`calls(rem)`-complexity of `Nat.Coprime` in the Euclidean structure `Nε` at `(a, b)` is the
length of a shortest remainder derivation of `1` from `a, b`. For non-coprime pairs both
sides are `0` by the `sInf ∅ = 0` convention. -/
theorem callsRem_eq_D (a b : ℕ) : callsRem a b = D a b := by
  rw [callsRem_eq_derivLen, D_eq_derivLen]

end ShortGCD
