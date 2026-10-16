import ShortGCD.Derivation

namespace ShortGCD

/-- A derivation can be run with any larger initial store. -/
theorem Derives.enlarge {S T n} (h : Derives S n T) {U : Finset ℕ} (hSU : S ⊆ U) :
    ∃ V, Derives U n V ∧ T ⊆ V := by
  refine ⟨T ∪ U, ?_, Finset.subset_union_left⟩
  simpa [Finset.union_eq_right.mpr hSU] using h.mono U

theorem Generates.enlarge {S k w} (h : Generates S k w) {U : Finset ℕ} (hSU : S ⊆ U) :
    Generates U k w := by
  obtain ⟨n,T,hn,hd,hw⟩ := h
  obtain ⟨V,hV,hTV⟩ := hd.enlarge hSU
  exact ⟨n,V,hn,hV,hTV hw⟩

/-- Any bounded derivation can be concatenated after an existing one. -/
theorem Derives.then_generate {S T n k w} (h : Derives S n T)
    (g : Generates T k w) : Generates S (n+k) w := by
  obtain ⟨j,U,hj,hd,hw⟩ := g
  exact ⟨n+j,U,Nat.add_le_add_left hj _,h.trans hd,hw⟩

/-- Euclid establishes existence; no arbitrary zero divisor is ever used. -/
theorem gcd_generatable (a b : ℕ) : ∃ k, Generates {a,b} k (Nat.gcd a b) := by
  induction a, b using Nat.gcd.induction with
  | H0 b => exact ⟨0, by simpa using Generates.available (S := {0,b}) (k := 0) (by simp : b ∈ ({0,b}:Finset ℕ))⟩
  | H1 a b ha ih =>
    obtain ⟨k,hk⟩ := ih
    have hd : Derives {a,b} 1 (insert (b%a) {a,b}) :=
      .step (.refl _) (by simp) (by simp) ha
    refine ⟨1+k, ?_⟩
    rw [Nat.gcd_rec]
    exact hd.then_generate (hk.enlarge (by intro z hz; simp at hz ⊢; tauto))

/-- The least number of remainder calls generating the gcd. -/
noncomputable def G (a b : ℕ) : ℕ := by
  classical
  exact Nat.find (gcd_generatable a b)

theorem generates_G (a b : ℕ) : Generates {a,b} (G a b) (Nat.gcd a b) := by
  classical
  exact Nat.find_spec (gcd_generatable a b)

theorem G_le {a b k} (h : Generates {a,b} k (Nat.gcd a b)) : G a b ≤ k := by
  classical
  exact Nat.find_min' (gcd_generatable a b) h

/-- A size bound for generating gcds; it applies to zero and unordered inputs too. -/
def GBound (M K : ℕ) : Prop := ∀ a b, a ≤ M → b ≤ M → Generates {a,b} K (Nat.gcd a b)

/-- Two calls and two recursive derivations finish from any small available modulus.
There is no coprimality assumption on the modulus. -/
theorem finish_from_modulus {S : Finset ℕ} {a b m M K : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hm : m ∈ S) (hp : 0 < m) (hM : m ≤ M)
    (hK : GBound M K) : Generates S (2+K+K) (Nat.gcd m (Nat.gcd a b)) := by
  let u := a % m
  let v := b % m
  have hu : u ≤ M := (Nat.mod_lt a hp).le.trans hM
  have hv : v ≤ M := (Nat.mod_lt b hp).le.trans hM
  have hd₁ : Derives S 1 (insert u S) := .step (.refl _) ha hm hp
  have hd₂ : Derives S 2 (insert v (insert u S)) :=
    .step hd₁ (Finset.mem_insert_of_mem hb) (Finset.mem_insert_of_mem hm) hp
  obtain ⟨n,T,hn,hd,hdmem⟩ := (hK m u hM hu).enlarge
    (show ({m,u}:Finset ℕ) ⊆ insert v (insert u S) from by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      rcases hz with rfl | rfl <;> simp [hm])
  have hvT : v ∈ T := hd.subset (by simp)
  have hdM : Nat.gcd m u ≤ M := (Nat.gcd_le_left u hp).trans hM
  have hg := (hK (Nat.gcd m u) v hdM hv).enlarge
    (show ({Nat.gcd m u,v}:Finset ℕ) ⊆ T from by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption)
  have hfinish := (hd₂.trans hd).then_generate hg
  have he : Nat.gcd (Nat.gcd m u) v = Nat.gcd m (Nat.gcd a b) := gcd_recombine a b m
  rw [he] at hfinish
  exact hfinish.mono_cost (by omega)

end ShortGCD
