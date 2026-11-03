module

public import PaperP1.Model.ConnectedComplementDeficit
public import PaperP1.Model.CompressedJointMoments
public import PaperP1.Model.FamilyIndependentMass
public import PaperP1.Combinatorics.RestrictedSeedComplements

/-! # Actual incompatible connected activity is charged to proper centered sources and their failed independent complements -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IncompatibleConnectedDeficit

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.ConnectedWindowFamilies

def sources (G : Finset ℕ) (r : ℕ) : Finset (Finset ℕ) := by
  classical
  exact G.powerset.filter fun D ↦ D.Nonempty ∧ D.card < r

theorem mem_sources (G D : Finset ℕ) (r : ℕ) :
    D ∈ sources G r ↔ D ⊆ G ∧ D.Nonempty ∧ D.card < r := by
  classical
  simp only [sources, mem_filter, mem_powerset]

theorem proper_bound (L : ℕ) (I : Finset ℕ) (hq : infiniteJointMoment L I = 0) :
    |infiniteCenteredCoefficient L I| ≤
      ∑ D ∈ I.powerset.erase I, |infiniteCenteredCoefficient L D| * ∏ x ∈ I \ D, infiniteMarginal x L := by
  classical
  let f := fun D : Finset ℕ ↦ infiniteCenteredCoefficient L D * ∏ x ∈ I \ D, infiniteMarginal x L
  have hexp := CompressedJointMoments.infinite_uncentered_expansion L I
  have hsplit := sum_erase_add I.powerset f (mem_powerset_self I)
  have hsum : (∑ D ∈ I.powerset.erase I, f D) + infiniteCenteredCoefficient L I = 0 := by
    simpa only [f, hq, sdiff_self, bot_eq_empty, prod_empty, mul_one] using hsplit.trans hexp.symm
  have heq : infiniteCenteredCoefficient L I = -(∑ D ∈ I.powerset.erase I, f D) :=
    eq_neg_of_add_eq_zero_right hsum
  rw [heq, abs_neg]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro D _hD
  dsimp only [f]
  rw [abs_mul, abs_of_nonneg (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)]

theorem finite_bound (G : Finset ℕ) (L r : ℕ) (hr : 1 ≤ r) (F : Finset (Finset ℕ))
    (hF : F ⊆ connectedFamilies G L r) (hq : ∀ I ∈ F, infiniteJointMoment L I = 0) :
    (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ FamilyIndependentMass.independentMass F L +
      ∑ D ∈ sources G r, |infiniteCenteredCoefficient L D| *
        IndependentExtensionDeficit.deficit G D (span (fun x ↦ squareClassSpace x L) D) L 1 := by
  classical
  let b := fun D I : Finset ℕ ↦ if D ⊂ I then
    |infiniteCenteredCoefficient L D| * ∏ x ∈ I \ D, infiniteMarginal x L else 0
  have hb (D I : Finset ℕ) : 0 ≤ b D I := by
    dsimp [b]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    · exact le_rfl
  have hpoint (I : Finset ℕ) (hI : I ∈ F) : |infiniteCenteredCoefficient L I| ≤
      (∏ x ∈ I, infiniteMarginal x L) + ∑ D ∈ sources G r, b D I := by
    have hIF := hF hI
    obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp (mem_filter.mp hIF).1
    have hne : I ≠ ∅ := (card_pos.mp (by omega : 0 < I.card)).ne_empty
    let A := (I.powerset.erase I).erase ∅
    have hempty : (∅ : Finset ℕ) ∈ I.powerset.erase I := mem_erase.mpr ⟨hne.symm, empty_mem_powerset I⟩
    have hsplit := sum_erase_add (I.powerset.erase I)
      (fun D ↦ |infiniteCenteredCoefficient L D| * ∏ x ∈ I \ D, infiniteMarginal x L) hempty
    simp only [CompressedJointMoments.centered_empty, abs_one, sdiff_empty, one_mul] at hsplit
    have hAData (D : Finset ℕ) (hD : D ∈ A) : D ⊂ I ∧ D.Nonempty := by
      obtain ⟨hDne, hD⟩ := mem_erase.mp hD
      obtain ⟨hDI, hDPow⟩ := mem_erase.mp hD
      exact ⟨Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp hDPow, hDI⟩, nonempty_iff_ne_empty.mpr hDne⟩
    have hASub : A ⊆ sources G r := by
      intro D hD
      have hd := hAData D hD
      exact (mem_sources G D r).mpr ⟨hd.1.subset.trans hIG, hd.2, by
        have h := card_lt_card hd.1; omega⟩
    have hASum : (∑ D ∈ A, |infiniteCenteredCoefficient L D| * ∏ x ∈ I \ D, infiniteMarginal x L) ≤
        ∑ D ∈ sources G r, b D I := by
      calc
        _ = ∑ D ∈ A, b D I := sum_congr rfl (fun D hD ↦ by simp only [b, ite_eq_left (hAData D hD).1])
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg hASub (fun D _ _ ↦ hb D I)
    have hproper := proper_bound L I (hq I hI)
    change (∑ D ∈ A, |infiniteCenteredCoefficient L D| * ∏ x ∈ I \ D, infiniteMarginal x L) + _ = _ at hsplit
    linarith only [hproper, hsplit, hASum]
  have hcell (D : Finset ℕ) (hD : D ∈ sources G r) :
      (∑ I ∈ F, b D I) ≤ |infiniteCenteredCoefficient L D| *
        IndependentExtensionDeficit.deficit G D (span (fun x ↦ squareClassSpace x L) D) L 1 := by
    have hd := (mem_sources G D r).mp hD
    let T := F.filter fun I ↦ D ⊂ I
    have hf : (∑ I ∈ T, ∏ x ∈ I \ D, infiniteMarginal x L) ≤
        ∑ U ∈ IndependentExtensionDeficit.families (G \ D) (span (fun x ↦ squareClassSpace x L) D) L,
          ∏ x ∈ U, infiniteMarginal x L := by
      apply RestrictedSeedComplements.fiber_bound T D _ (fun x ↦ infiniteMarginal x L)
        (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      intro I hI
      obtain ⟨hIF, hproper⟩ := mem_filter.mp hI
      have hconn := (mem_filter.mp (hF hIF)).2
      have hIG := (mem_powersetCard.mp (mem_filter.mp (hF hIF)).1).1
      exact ⟨hproper.subset, ConnectedComplementDeficit.complement_mem G L I D hIG hproper hd.2.1 hconn⟩
    calc
      _ = |infiniteCenteredCoefficient L D| * ∑ I ∈ T, ∏ x ∈ I \ D, infiniteMarginal x L := by
        simp only [b, T, sum_filter, mul_sum, mul_ite, mul_zero]
      _ ≤ |infiniteCenteredCoefficient L D| *
          ∑ U ∈ IndependentExtensionDeficit.families (G \ D) (span (fun x ↦ squareClassSpace x L) D) L,
            ∏ x ∈ U, infiniteMarginal x L := mul_le_mul_of_nonneg_left hf (abs_nonneg _)
      _ = _ := by simp only [IndependentExtensionDeficit.deficit, one_pow, one_mul]
  calc
    _ ≤ ∑ I ∈ F, ((∏ x ∈ I, infiniteMarginal x L) + ∑ D ∈ sources G r, b D I) := sum_le_sum hpoint
    _ = FamilyIndependentMass.independentMass F L + ∑ D ∈ sources G r, ∑ I ∈ F, b D I := by
      rw [sum_add_distrib, sum_comm]
      rfl
    _ ≤ _ := add_le_add le_rfl (sum_le_sum hcell)

end PaperP1.IncompatibleConnectedDeficit
