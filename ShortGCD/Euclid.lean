import ShortGCD.Contraction
import ShortGCD.Normalization

/-! # The Euclidean remainder sequence

`remainder a b i` is the Euclidean remainder `r_i`, and `euclidStore a b n` holds
`r_0, …, r_{n+1}`, derived with `n` calls. `euclid_dichotomy` splits a coprime input: either
some early remainder pair is small (`≤ L`) and coprime, or the remainders `r_0, …, r_h` all
exceed `L` and form the prefix used by the large branch in `FiniteBound`.
-/

namespace ShortGCD

def euclidPair (a b : ℕ) : ℕ → ℕ × ℕ
  | 0 => (a,b)
  | n+1 => ((euclidPair a b n).2, (euclidPair a b n).1 % (euclidPair a b n).2)

/-- The Euclidean remainder `r_i`: `r_0 = a`, `r_1 = b`, `r_{i+2} = r_i mod r_{i+1}`. -/
def remainder (a b i : ℕ) : ℕ := (euclidPair a b i).1

@[simp] theorem remainder_zero (a b) : remainder a b 0 = a := rfl
@[simp] theorem remainder_one (a b) : remainder a b 1 = b := rfl

theorem remainder_rec (a b i) :
    remainder a b (i+2) = remainder a b i % remainder a b (i+1) := rfl

theorem remainder_gcd (a b i) :
    Nat.gcd (remainder a b i) (remainder a b (i+1)) = Nat.gcd a b := by
  induction i with
  | zero => rfl
  | succ i ih => rw [remainder_rec, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]; exact ih

theorem remainder_bound {a b} (hab : b ≤ a) (i) : remainder a b i ≤ a := by
  induction i using Nat.twoStepInduction with
  | zero => simp
  | one => simpa
  | more i hi hi' => exact (Nat.mod_le _ _).trans hi

/-- The store `{r_0, …, r_{n+1}}`. -/
def euclidStore (a b n : ℕ) : Finset ℕ := (Finset.range (n+2)).image (remainder a b)

@[simp] theorem euclidStore_zero (a b) : euclidStore a b 0 = {a,b} := by
  simp [euclidStore, Finset.range_add_one, Finset.image_insert, Finset.pair_comm]

theorem mem_euclidStore {a b n i} (hi : i < n+2) : remainder a b i ∈ euclidStore a b n :=
  Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)

theorem euclidStore_succ (a b n) : euclidStore a b (n+1) =
    insert (remainder a b (n+2)) (euclidStore a b n) := by
  simp only [euclidStore, show n+1+2 = (n+2)+1 from by omega,
    Finset.range_add_one, Finset.image_insert]

theorem euclid_derives (a b n) (hp : ∀ i, i < n → 0 < remainder a b (i+1)) :
    Derives {a,b} n (euclidStore a b n) := by
  induction n with
  | zero => simpa using Derives.refl ({a,b}:Finset ℕ)
  | succ n ih =>
      rw [euclidStore_succ, remainder_rec]
      exact .step (ih (fun i hi => hp i (by omega)))
        (mem_euclidStore (by omega)) (mem_euclidStore (by omega)) (hp n (by omega))

/-- Conditional strict decrease, before the first zero remainder. -/
theorem remainder_desc {a b h} (hab : b < a)
    (hp : ∀ i, i < h → 0 < remainder a b (i+1)) :
    ∀ i, i < h → remainder a b (i+1) < remainder a b i := by
  intro i hi
  cases i with
  | zero => exact hab
  | succ i => exact Nat.mod_lt _ (hp i (by omega))

theorem remainder_lower {a b h} (hab : b < a)
    (hp : ∀ i, i < h → 0 < remainder a b (i+1)) :
    ∀ i, i ≤ h → remainder a b h ≤ remainder a b i := by
  intro i hi
  induction h, hi using Nat.le_induction with
  | base => exact le_rfl
  | succ h hih ih =>
      have hhp : ∀ j, j < h → 0 < remainder a b (j+1) := fun j hj => hp j (by omega)
      exact (remainder_desc hab hp h (by omega)).le.trans (ih hhp)

/-- A first crossing of a positive threshold gives a small coprime subproblem.
The other branch gives a genuine positive Euclidean prefix. -/
theorem euclid_dichotomy {a b h L : ℕ} (hab : b < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b) (hL : 1 ≤ L) (hh : 0 < h) :
    (∃ c s n T, n ≤ h+1 ∧ Derives {a,b} n T ∧ c ∈ T ∧ s ∈ T ∧
      c ≤ L ∧ s ≤ L ∧ Nat.Coprime c s) ∨
    ((∀ i, i ≤ h → L < remainder a b i) ∧
      Derives {a,b} h (euclidStore a b h)) := by
  by_cases hearly : ∃ i, i < h ∧ remainder a b (i+1) ≤ L
  · classical
    let i := Nat.find hearly
    have hi : i < h ∧ remainder a b (i+1) ≤ L := Nat.find_spec hearly
    have hprev : ∀ j, j < i → L < remainder a b (j+1) := by
      intro j hj
      have hh := Nat.find_min hearly hj
      dsimp [i] at hj
      omega
    have hp : 0 < remainder a b (i+1) := by
      by_contra! hz
      have heq : remainder a b (i+1) = 0 := by omega
      have hg := remainder_gcd a b i
      rw [heq,Nat.gcd_zero_right,hcop.gcd_eq_one] at hg
      by_cases hi0 : i = 0
      · simp [hi0] at heq
        omega
      · have hh := hprev (i-1) (by omega)
        have hie : i-1+1 = i := by omega
        rw [hie,hg] at hh
        omega
    have hpos : ∀ j, j < i+1 → 0 < remainder a b (j+1) := by
      intro j hj
      by_cases hj' : j < i
      · have := hprev j hj'; omega
      · have : j = i := by omega
        simpa [this] using hp
    left
    refine ⟨remainder a b (i+1),remainder a b (i+2),i+1,euclidStore a b (i+1),
      by omega,euclid_derives a b (i+1) hpos,mem_euclidStore (by omega),
      mem_euclidStore (by omega),hi.2,?_,?_⟩
    · exact (Nat.mod_lt _ hp).le.trans hi.2
    · exact (remainder_gcd a b (i+1)).trans hcop.gcd_eq_one
  · have hp : ∀ i, i < h → L < remainder a b (i+1) := by
      intro i hi
      exact lt_of_not_ge (fun hh => hearly ⟨i,hi,hh⟩)
    right
    refine ⟨?_,euclid_derives a b h (fun i hi => lt_trans (by omega) (hp i hi))⟩
    intro i hi
    cases i with
    | zero => exact (hp 0 hh).trans hab
    | succ i => exact hp i (by omega)

end ShortGCD
