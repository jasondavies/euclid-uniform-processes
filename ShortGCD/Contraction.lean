import ShortGCD.Gap
import ShortGCD.Composition
import ShortGCD.Prefix

namespace ShortGCD

/-- Every modulus above L sees at least k+1 residue classes in the reservoir. -/
def Reservoir (R : Finset ℕ) (L k : ℕ) : Prop :=
  ∀ m, L < m → k+1 ≤ (R.image (fun x => x % m)).card

theorem Reservoir.contract {R S : Finset ℕ} {L k m : ℕ}
    (hR : Reservoir R L k) (hRS : R ⊆ S) (hk : 1 ≤ k)
    (hm : m ∈ S) (hL : L < m) :
    ∃ w, 0 < w ∧ w*k < m ∧ Generates S 3 w := by
  have ht := (hR m hL).trans (Finset.card_le_card (Finset.image_subset_image hRS))
  obtain ⟨w,hw,hwsmall,hgen⟩ := small_remainder S (by omega) hm (by omega)
  refine ⟨w,hw,?_,hgen⟩
  exact (Nat.mul_le_mul_left w (by omega : k ≤ (S.image (fun x => x % m)).card-1)).trans_lt hwsmall

/-- Reusing the same reservoir gives at most 3J calls to reach the target size. -/
theorem Reservoir.iterate {R : Finset ℕ} {L k : ℕ} (hR : Reservoir R L k)
    (hk : 1 ≤ k) (J : ℕ) :
    ∀ S : Finset ℕ, R ⊆ S → ∀ m ∈ S, 0 < m → m ≤ L*k^J →
    ∃ w, 0 < w ∧ w ≤ L ∧ Generates S (3*J) w := by
  induction J with
  | zero =>
      intro S hRS m hm hp hsize
      exact ⟨m,hp,by simpa using hsize,Generates.available hm⟩
  | succ J ih =>
      intro S hRS m hm hp hsize
      by_cases hsmall : m ≤ L
      · exact ⟨m,hp,hsmall,Generates.available hm⟩
      obtain ⟨w,hw,hwk,n,T,hn,hd,hwT⟩ := hR.contract hRS hk hm (by omega)
      have hwsize : w ≤ L*k^J := by
        rw [pow_succ, ← Nat.mul_assoc] at hsize
        have : w*k < (L*k^J)*k := hwk.trans_le hsize
        exact (Nat.lt_of_mul_lt_mul_right this).le
      obtain ⟨z,hz,hzL,hgen⟩ := ih T (hRS.trans hd.subset) w hwT hw hwsize
      exact ⟨z,hz,hzL,(hd.then_generate hgen).mono_cost (by omega)⟩

/-- The Euclidean prefix is a reservoir for every sufficiently large modulus. -/
theorem prefix_reservoir (r q : ℕ → ℕ) (a h L k : ℕ)
    (hpos : ∀ i, i ≤ h → 0 < r i)
    (hbound : ∀ i, i ≤ h → r i ≤ a)
    (hlower : ∀ i, i ≤ h → r h ≤ r i)
    (hcop : ∀ i, i < h → Nat.Coprime (r i) (r (i+1)))
    (hq : ∀ i, i+2 ≤ h → 0 < q i)
    (heq : ∀ i, i+2 ≤ h → r i = q i*r (i+1)+r (i+2))
    (hL : 2*a ≤ L*r h) (hsize : k^2 < h) :
    Reservoir ((Finset.range (h+1)).image r) L k := by
  intro m hm
  have hm' : 2*a < m*r h := hL.trans_lt
    (Nat.mul_lt_mul_of_pos_right hm (hpos h le_rfl))
  have hinj := prefix_pairs_distinct r q a h m hpos hbound hlower hcop hq heq hm'
  have hcard := residue_card_sq r h m hinj
  have he : (((Finset.range (h+1)).image r).image (fun x => x % m)) =
      (Finset.range (h+1)).image (fun i => r i % m) := by simp only [Finset.image_image, Function.comp_def]
  rw [he]
  nlinarith

/-- Complete large-prefix branch, with all costs and operand availability explicit.
`H` counts the already constructed prefix; `J` counts contractions; `K` bounds
both recursive gcd derivations. -/
theorem large_branch {S T R : Finset ℕ} {a b m H L k J K : ℕ}
    (hprefix : Derives S H T) (ha : a ∈ T) (hb : b ∈ T)
    (hm : m ∈ T) (hp : 0 < m) (hRT : R ⊆ T)
    (hR : Reservoir R L k) (hk : 1 ≤ k) (hsize : m ≤ L*k^J)
    (hK : GBound L K) (hcop : Nat.Coprime a b) :
    Generates S (H+3*J+2+2*K) 1 := by
  obtain ⟨w,hw,hwL,n,U,hn,hd,hwU⟩ := hR.iterate hk J T hRT m hm hp hsize
  have hfinish := finish_from_modulus (hd.subset ha) (hd.subset hb) hwU hw hwL hK
  rw [hcop.gcd_eq_one, Nat.gcd_one_right] at hfinish
  exact ((hprefix.trans hd).then_generate hfinish).mono_cost (by omega)

end ShortGCD
