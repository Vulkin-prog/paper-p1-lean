module

public import PaperP1.Affine.RetainedNullity
public import PaperP1.Algebra.StoppedExpansion

/-! # Heredity and the unique dependent pair of the first retained class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedDependence

open Finset PaperP1.Affine PaperP1.RetainedNullity

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

def Compressed (e I : Finset ι) : Prop := e ⊆ I ∧ relativeNullityOn S I = relativeNullityOn S e

def Retained (E : Finset (Finset ι)) (I : Finset ι) : Prop :=
  relativeNullityOn S I = 0 ∨ ∃ e ∈ E, Compressed S e I

theorem pair_inter_card_le_one (e J : Finset ι) (he : e.card = 2) (hne : ¬e ⊆ J) :
    (e ∩ J).card ≤ 1 := by
  have hlt : (e ∩ J).card < e.card := by
    apply Finset.card_lt_card
    apply ssubset_iff_subset_not_subset.mpr
    refine ⟨inter_subset_left, ?_⟩
    intro hsub
    exact hne (hsub.trans inter_subset_right)
  omega

theorem compressed_subfamily (e I J : Finset ι) (he : e.card = 2)
    (hcomp : Compressed S e I) (hJI : J ⊆ I) :
    relativeNullityOn S J = 0 ∨ Compressed S e J := by
  by_cases heJ : e ⊆ J
  · right
    refine ⟨heJ, ?_⟩
    have hlo := relativeNullityOn_mono S heJ
    have hhi := relativeNullityOn_mono S hJI
    have hnull := hcomp.2
    omega
  · left
    have hsmall := pair_inter_card_le_one e J he heJ
    have hnull := nullity_card_le_one S (e ∩ J) hsmall
    have hrestrict := compressed_restriction S e I J hcomp.1 hJI hcomp.2
    rw [inter_comm] at hnull
    exact hrestrict.trans hnull

theorem hereditary (E : Finset (Finset ι)) (hE : ∀ e ∈ E, e.card = 2) :
    PaperP1.Algebra.Hereditary (Retained S E) := by
  intro I J hJI hI
  rcases hI with hzero | ⟨e, he, hcomp⟩
  · left
    have hmono := relativeNullityOn_mono S hJI
    omega
  · rcases compressed_subfamily S e I J (hE e he) hcomp hJI with hzero | hsmall
    · exact Or.inl hzero
    · exact Or.inr ⟨e, he, hsmall⟩

theorem dependent_pair_unique (E : Finset (Finset ι)) (hE : ∀ e ∈ E, e.card = 2)
    (I : Finset ι) (hI : Retained S E I) (hnot : relativeNullityOn S I ≠ 0) :
    ∃ e ∈ E, Compressed S e I ∧ 0 < relativeNullityOn S e ∧
      ∀ q : Finset ι, q ⊆ I → q.card = 2 → 0 < relativeNullityOn S q → q = e := by
  rcases hI with hzero | ⟨e, heE, heI, hnull⟩
  · exact False.elim (hnot hzero)
  · refine ⟨e, heE, ⟨heI, hnull⟩, Nat.pos_of_ne_zero (by omega), ?_⟩
    intro q hqI hqcard hqpos
    by_cases heq : e ⊆ q
    · exact (eq_of_subset_of_card_le heq (by rw [hqcard, hE e heE])).symm
    · have hsmall := pair_inter_card_le_one e q (hE e heE) heq
      have hzero := nullity_card_le_one S (e ∩ q) hsmall
      have hrestrict := compressed_restriction S e I q heI hqI hnull
      rw [inter_comm] at hzero
      omega

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
theorem retained_nullity_le (E : Finset (Finset ι)) (R : ℝ) (hR : 0 ≤ R)
    (hE : ∀ e ∈ E, (relativeNullityOn S e : ℝ) ≤ R)
    (I : Finset ι) (hI : Retained S E I) : (relativeNullityOn S I : ℝ) ≤ R := by
  rcases hI with hzero | ⟨e, he, hcomp⟩
  · simpa only [hzero, Nat.cast_zero] using hR
  · rw [hcomp.2]
    exact hE e he

section Ordered

variable [LinearOrder ι]

omit [DecidableEq ι] in
theorem boundary_nullity_bound (E : Finset (Finset ι)) (R L : ℝ) (hR : 0 ≤ R)
    (hE : ∀ e ∈ E, (relativeNullityOn S e : ℝ) ≤ R)
    (I : Finset ι) (hI : PaperP1.Algebra.OrderedBoundary (Retained S E) I)
    (hlocal : ∀ i ∈ I, (Module.finrank 𝔽₂ (S i) : ℝ) ≤ L) :
    0 < relativeNullityOn S I ∧ (relativeNullityOn S I : ℝ) ≤ R + L := by
  have hempty : Retained S E ∅ := Or.inl (relativeNullityOn_empty S)
  have hne := PaperP1.Algebra.orderedBoundary_nonempty hempty hI
  let i := I.max' hne
  have hi : i ∈ I := I.max'_mem hne
  have hpref : Retained S E (I.erase i) := by
    simpa only [PaperP1.Algebra.properPrefix_eq_erase_max I hne] using hI.2
  have hbase := retained_nullity_le S E R hR hE (I.erase i) hpref
  have hstep := nullity_insert_le S i (I.erase i)
  rw [insert_erase hi] at hstep
  have hreal : (relativeNullityOn S I : ℝ) ≤
      (relativeNullityOn S (I.erase i) : ℝ) + Module.finrank 𝔽₂ (S i) := by exact_mod_cast hstep
  refine ⟨Nat.pos_of_ne_zero (fun hz ↦ hI.1 (Or.inl hz)), ?_⟩
  exact hreal.trans (add_le_add hbase (hlocal i hi))

end Ordered

end PaperP1.RetainedDependence
