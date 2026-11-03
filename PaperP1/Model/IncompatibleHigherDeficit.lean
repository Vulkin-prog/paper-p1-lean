module

public import PaperP1.Model.IncompatibleConnectedDeficit
public import PaperP1.Model.AllPairDeficitMonotonicity
public import PaperP1.Model.ActualCanonicalComponents

/-! # Separate actual pair deficits before estimating the higher proper sources -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IncompatibleHigherDeficit

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.ConnectedWindowFamilies

def higherSources (G : Finset ℕ) (r : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (IncompatibleConnectedDeficit.sources G r).filter fun D ↦ 3 ≤ D.card

theorem finite_bound (G : Finset ℕ) (L r : ℕ) (hr : 1 ≤ r) (F : Finset (Finset ℕ))
    (hF : F ⊆ connectedFamilies G L r) (hq : ∀ I ∈ F, infiniteJointMoment L I = 0) :
    (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ FamilyIndependentMass.independentMass F L +
      AllPairExtensionDeficit.deficit G L 1 +
      ∑ D ∈ higherSources G r, |infiniteCenteredCoefficient L D| *
        IndependentExtensionDeficit.deficit G D (span (fun x ↦ squareClassSpace x L) D) L 1 := by
  classical
  let S := IncompatibleConnectedDeficit.sources G r
  let w := fun D ↦ |infiniteCenteredCoefficient L D| *
    IndependentExtensionDeficit.deficit G D (span (fun x ↦ squareClassSpace x L) D) L 1
  have hw (D : Finset ℕ) : 0 ≤ w D := mul_nonneg (abs_nonneg _)
    (IndependentDeficitMonotonicity.nonneg G D _ L 1 (by norm_num))
  let P := fun D : Finset ℕ ↦ D.card = 2
  have hpair : (∑ D ∈ S.filter P, w D) ≤ AllPairExtensionDeficit.deficit G L 1 := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro D hD
      obtain ⟨hDS, hcard⟩ := mem_filter.mp hD
      exact mem_powersetCard.mpr ⟨((IncompatibleConnectedDeficit.mem_sources G D r).mp hDS).1, hcard⟩
    · intro D _ _
      exact hw D
  have hsub : higherSources G r ⊆ S.filter fun D ↦ ¬ P D := by
    intro D hD
    obtain ⟨hDS, hcard⟩ := mem_filter.mp hD
    exact mem_filter.mpr ⟨hDS, by dsimp [P]; omega⟩
  have hrest : (∑ D ∈ S.filter (fun D ↦ ¬ P D), w D) = ∑ D ∈ higherSources G r, w D := by
    symm
    apply sum_subset hsub
    intro D hD hnot
    obtain ⟨hDS, hcard2⟩ := mem_filter.mp hD
    have hne := ((IncompatibleConnectedDeficit.mem_sources G D r).mp hDS).2.1
    have hsmall : D.card < 3 := by
      by_contra h
      exact hnot (mem_filter.mpr ⟨hDS, by omega⟩)
    have hcard : D.card = 1 := by have hpos := hne.card_pos; dsimp [P] at hcard2; omega
    obtain ⟨x, rfl⟩ := card_eq_one.mp hcard
    dsimp only [w]
    rw [ActualCanonicalComponents.singleton_zero, abs_zero, zero_mul]
  have hsplit := sum_filter_add_sum_filter_not S P w
  have hfinite := IncompatibleConnectedDeficit.finite_bound G L r hr F hF hq
  change (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤
    FamilyIndependentMass.independentMass F L + ∑ D ∈ S, w D at hfinite
  rw [hrest] at hsplit
  linarith only [hfinite, hpair, hsplit]

end PaperP1.IncompatibleHigherDeficit
