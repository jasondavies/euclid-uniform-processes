module

public import ShortGCD.Asymptotic
public import ShortGCD.GcdCertificate

@[expose] public section

/-! # From derivations to certificates

A derivation with `k` calls yields a sound set of at most `k` remainder facts, and reachability
in a sound set of facts yields a derivation (`generates_of_reach`). So for `a > 0` some gcd
certificate has at most `G a b + 2` remainder facts, every gcd certificate has at least
`G a b`, and `G = D` on coprime pairs. `Conjecture` uses these to bound the intrinsic
complexities.
-/

namespace ShortGCD

open Finset

/-- A sequential derivation determines at most one remainder fact per call. -/
theorem Derives.to_facts {S T n a b} (h : Derives S n T) :
    ∀ F₀ : Finset RemFact, SoundRems F₀ → (∀ z ∈ S, Reach F₀ a b z) →
    ∃ F : Finset RemFact, SoundRems F ∧ F.card ≤ F₀.card+n ∧ ∀ z ∈ T, Reach F a b z := by
  induction h with
  | refl => intro F hF hS; exact ⟨F,hF,by omega,hS⟩
  | @step T n x y h hx hy hp ih =>
    intro F₀ hF₀ hS
    obtain ⟨F,hF,hcard,hreach⟩ := ih F₀ hF₀ hS
    let F' := insert (x,y,x%y) F
    refine ⟨F',?_,?_,?_⟩
    · intro f hf
      rcases mem_insert.mp hf with rfl | hf
      · exact ⟨hp.ne',rfl⟩
      · exact hF f hf
    · have hh := card_insert_le (x,y,x%y) F
      dsimp [F']
      omega
    · intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · exact .step (mem_insert_self _ _) ((hreach x hx).mono (subset_insert _ _))
          ((hreach y hy).mono (subset_insert _ _))
      · exact (hreach z hz).mono (subset_insert _ _)

theorem Generates.to_facts {a b w k} (h : Generates {a,b} k w) :
    ∃ F : Finset RemFact, SoundRems F ∧ F.card ≤ k ∧ Reach F a b w := by
  obtain ⟨n,T,hn,hd,hw⟩ := h
  obtain ⟨F,hF,hcard,hreach⟩ := hd.to_facts ∅ (by simp [SoundRems]) (by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact .left
    · exact .right)
  exact ⟨F,hF,by simpa using hcard.trans (by simpa using hn),hreach w hw⟩

/-- General gcd certificate from a derivation, in the remainder/zero-test structure.
The empty `eq1s` field makes the absence of one-tests explicit. -/
theorem gcd_certificate_of_facts {F : Finset RemFact} {a b : ℕ}
    (hp : 0 < Nat.gcd a b) (hF : SoundRems F) (hg : Reach F a b (Nat.gcd a b)) :
    ∃ U : Cert, U.CertifiesGcd a b ∧ U.eq1s = ∅ ∧ U.rems.card ≤ F.card+2 := by
  classical
  let g := Nat.gcd a b
  let Q := F.filter fun f => Reach F a b f.1 ∧ Reach F a b f.2.1
  let R := insert (a,g,0) (insert (b,g,0) Q)
  have hQR : Q ⊆ R := (subset_insert _ _).trans (subset_insert _ _)
  have hgR : Reach R a b g := hg.filter.mono hQR
  have haR : (a,g,0) ∈ R := mem_insert_self _ _
  have hbR : (b,g,0) ∈ R := mem_insert_of_mem (mem_insert_self _ _)
  refine ⟨⟨R,{(0,true)},∅⟩,⟨⟨?_,by simp,by simp⟩,⟨?_,?_,by simp⟩,hgR,?_⟩,rfl,?_⟩
  · intro f hf
    rcases mem_insert.mp hf with rfl | hf
    · exact ⟨hp.ne', (Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left a b)).symm⟩
    rcases mem_insert.mp hf with rfl | hf
    · exact ⟨hp.ne', (Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right a b)).symm⟩
    exact hF f (mem_filter.mp hf).1
  · intro f hf
    rcases mem_insert.mp hf with rfl | hf
    · exact ⟨.left,hgR⟩
    rcases mem_insert.mp hf with rfl | hf
    · exact ⟨.right,hgR⟩
    obtain ⟨_,hx,hy⟩ := mem_filter.mp hf
    exact ⟨hx.filter.mono hQR,hy.filter.mono hQR⟩
  · intro p hp
    rw [mem_singleton.mp hp]
    exact .step haR .left hgR
  · intro π hπ
    obtain ⟨hrem,hzero,_⟩ := hπ
    have hz : π 0 = 0 := by simpa using hzero (0,true) (by simp)
    have ha : π g ∣ π a := Nat.dvd_of_mod_eq_zero (by
      simpa [hz] using (hrem (a,g,0) haR).2.symm)
    have hb : π g ∣ π b := Nat.dvd_of_mod_eq_zero (by
      simpa [hz] using (hrem (b,g,0) hbR).2.symm)
    exact Nat.dvd_antisymm (Nat.dvd_gcd ha hb)
      (Reach.dvd hrem (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) hgR)
  · have h₁ := card_insert_le (a,g,0) (insert (b,g,0) Q)
    have h₂ := card_insert_le (b,g,0) Q
    have h₃ : Q.card ≤ F.card := card_filter_le _ _
    dsimp only [R]
    omega

/-- The gcd certificate bound, for every `a > 0` and every `b`. -/
theorem gcd_certificate_bound {a b : ℕ} (ha : 0 < a) :
    ∃ U : Cert, U.CertifiesGcd a b ∧ U.eq1s = ∅ ∧ U.rems.card ≤ G a b+2 := by
  obtain ⟨F,hF,hcard,hg⟩ := (generates_G a b).to_facts
  obtain ⟨U,hU,h1,hcardU⟩ := gcd_certificate_of_facts (Nat.gcd_pos_of_pos_left b ha) hF hg
  exact ⟨U,hU,h1,by omega⟩

/-- For coprime `a, b`, some certificate of `Nat.Coprime a b` has at most `G a b` remainder facts. -/
theorem coprime_certificate_bound {a b : ℕ} (hc : Nat.Coprime a b) :
    ∃ U : Cert, U.CertifiesCoprime a b ∧ U.rems.card ≤ G a b := by
  obtain ⟨F,hF,hcard,hg⟩ := (generates_G a b).to_facts
  apply (exists_cert_iff a b (G a b)).mpr
  exact ⟨F,hF,by simpa [hc.gcd_eq_one] using hg,hcard⟩

/-- Some `C > 0` gives, for all `b ≤ a` with `a ≥ 4`, a gcd certificate without `eq1` facts
having at most `C log₂ a / log₂ log₂ a + 2` remainder facts. -/
theorem uniform_gcd_certificates : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ, 4 ≤ a → b ≤ a →
    ∃ U : Cert, U.CertifiesGcd a b ∧ U.eq1s = ∅ ∧
    (U.rems.card : ℝ) ≤ C*(Real.logb 2 a/Real.logb 2 (Real.logb 2 a))+2 := by
  obtain ⟨C,hC,hbound⟩ := uniform_real_bound
  refine ⟨C,hC,?_⟩
  intro a b ha hb
  obtain ⟨U,hU,h1,hcard⟩ := gcd_certificate_bound (a := a) (b := b) (by omega)
  refine ⟨U,hU,h1,?_⟩
  have hh : (U.rems.card:ℝ) ≤ (G a b:ℝ)+2 := by exact_mod_cast hcard
  linarith [hbound a b ha hb]

/-- For `a > 0` and non-coprime `a, b`, some sound certificate generated by `a, b`, with at most
`G a b + 2` remainder facts, forces every respecting map to send `a, b` to a non-coprime pair.
It is the gcd certificate plus the fact `eq1(gcd(a, b)) = ff`. -/
theorem noncoprime_certificate_bound {a b : ℕ} (ha : 0 < a)
    (hc : ¬ Nat.Coprime a b) :
    ∃ U : Cert, U.Sound ∧ U.Generated a b ∧ U.rems.card ≤ G a b+2 ∧
      ∀ π, U.Respects π → ¬ Nat.Coprime (π a) (π b) := by
  obtain ⟨U,hU,h1,hcard⟩ := gcd_certificate_bound (b := b) ha
  let V : Cert := { U with eq1s := {(Nat.gcd a b,false)} }
  refine ⟨V,⟨hU.1.1,hU.1.2.1,?_⟩,⟨hU.2.1.1,hU.2.1.2.1,?_⟩,hcard,?_⟩
  · intro p hp
    have he : p = (Nat.gcd a b,false) := mem_singleton.mp hp
    subst p
    simpa [Nat.Coprime] using hc
  · intro p hp
    rw [mem_singleton.mp hp]
    exact hU.2.2.1
  · intro π hπ hcop
    have hπU : U.Respects π := ⟨hπ.1,hπ.2.1,by simp [h1]⟩
    have he := hU.2.2.2 π hπU
    have hh := hπ.2.2 (Nat.gcd a b,false) (by simp [V])
    have hn : π (Nat.gcd a b) ≠ 1 := by simpa using hh
    exact hn (he.trans hcop.gcd_eq_one)

/-- Ordinary lists of remainder instructions run in the finite-store model. -/
theorem validFrom_derives {avail l : List ℕ} (h : ValidFrom avail l) :
    Derives avail.toFinset l.length (l.toFinset ∪ avail.toFinset) := by
  induction l generalizing avail with
  | nil => simpa using Derives.refl avail.toFinset
  | cons v rest ih =>
    obtain ⟨⟨x,hx,y,hy,hyp,hv⟩,hrest⟩ := h
    have hs : Derives avail.toFinset 1 (v::avail).toFinset := by
      simpa [hv] using Derives.step (.refl avail.toFinset)
        (List.mem_toFinset.mpr hx) (List.mem_toFinset.mpr hy) (Nat.pos_of_ne_zero hyp)
    have ht := hs.trans (ih hrest)
    simpa [Nat.add_comm,Finset.insert_union,Finset.union_insert] using ht

/-- Reachability in a finite sound diagram yields a derivation with at most as
many calls as there are remainder facts; repeated facts need not be executed. -/
theorem generates_of_reach {F : Finset RemFact} {a b w : ℕ} (hF : SoundRems F)
    (hw : Reach F a b w) : Generates {a,b} F.card w := by
  obtain ⟨l,hl,hwl,hnd,hfacts⟩ := exists_list_of_reach hF hw
  have hlen : l.length ≤ F.card := by
    calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
         _ ≤ (F.image fun f => f.2.2).card := card_le_card (by
           intro v hv
           obtain ⟨f,hf,he⟩ := hfacts v (List.mem_toFinset.mp hv)
           exact mem_image.mpr ⟨f,hf,he⟩)
         _ ≤ F.card := card_image_le
  refine ⟨l.length,l.toFinset ∪ {a,b},hlen,?_,?_⟩
  · simpa using validFrom_derives hl
  · simp only [List.mem_cons] at hwl
    simpa [or_assoc,or_comm,or_left_comm] using hwl

/-- Every certificate for `gcd(a, b)` has at least `G a b` remainder facts. -/
theorem gcd_certificate_lower {U : Cert} {a b} (hU : U.CertifiesGcd a b) :
    G a b ≤ U.rems.card := G_le (generates_of_reach hU.1.1 hU.2.2.1)

/-- Agreement with `D`, the shortest list derivation of `1`, on coprime inputs. -/
theorem G_eq_D {a b} (hc : Nat.Coprime a b) : G a b = D a b := by
  rw [D_eq_derivLen]
  apply Nat.le_antisymm
  · obtain ⟨F,hF,h1,hcard⟩ := Nat.sInf_mem (derivLen_set_nonempty hc)
    have hh := generates_of_reach hF h1
    rw [hcard] at hh
    apply G_le
    simpa [hc.gcd_eq_one,derivLen] using hh
  · obtain ⟨F,hF,hcard,hg⟩ := (generates_G a b).to_facts
    have hD : derivLen a b ≤ F.card := Nat.sInf_le
      ⟨F,hF,by simpa [hc.gcd_eq_one] using hg,rfl⟩
    exact hD.trans hcard

end ShortGCD
