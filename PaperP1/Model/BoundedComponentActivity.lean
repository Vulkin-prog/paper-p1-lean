module

public import PaperP1.Model.ActualCanonicalComponents
public import PaperP1.Combinatorics.FinitePolymerTail

/-! # Nonconnected actual centered activity is a quadratic tail of the bounded component population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedComponentActivity

open Finset PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies PaperP1.ActualCanonicalComponents

def population (G : Finset ℕ) (R : ℕ) : Finset (Finset ℕ) := by
  classical
  exact G.powerset.filter fun D ↦ 2 ≤ D.card ∧ D.card ≤ R

theorem sum_bound (G : Finset ℕ) (L R : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hcell : ∀ r : ℕ, 2 ≤ r → r ≤ R →
      (∑ D ∈ G.powersetCard r, |infiniteCenteredCoefficient L D|) ≤ B) :
    (∑ D ∈ population G R, |infiniteCenteredCoefficient L D|) ≤ ((R + 1 : ℕ) : ℝ) * B := by
  classical
  have hsplit := sum_fiberwise_of_maps_to (s := population G R) (t := Icc 2 R) (g := Finset.card)
    (fun D hD ↦ mem_Icc.mpr (mem_filter.mp hD).2) (fun D ↦ |infiniteCenteredCoefficient L D|)
  have hfiber (r : ℕ) (hr : r ∈ Icc 2 R) :
      (∑ D ∈ (population G R).filter (fun D ↦ D.card = r), |infiniteCenteredCoefficient L D|) ≤ B := by
    have hsub : (population G R).filter (fun D ↦ D.card = r) ⊆ G.powersetCard r := by
      intro D hD
      obtain ⟨hDG, hcard⟩ := mem_filter.mp hD
      exact mem_powersetCard.mpr ⟨mem_powerset.mp (mem_filter.mp hDG).1, hcard⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun D _ _ ↦ abs_nonneg _)).trans
      (hcell r (mem_Icc.mp hr).1 (mem_Icc.mp hr).2)
  calc
    _ = ∑ r ∈ Icc 2 R, ∑ D ∈ (population G R).filter (fun D ↦ D.card = r),
        |infiniteCenteredCoefficient L D| := hsplit.symm
    _ ≤ ∑ _r ∈ Icc 2 R, B := sum_le_sum hfiber
    _ = ((Icc 2 R).card : ℝ) * B := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show (Icc 2 R).card ≤ R + 1 by rw [Nat.card_Icc]; omega)) hB

theorem finite_bound (G : Finset ℕ) (L R : ℕ) (hL : 0 < L) (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I ⊆ G ∧ I.Nonempty ∧ I.card ≤ R ∧ ¬ Connected L I) :
    (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤
      ((∑ D ∈ population G R, |infiniteCenteredCoefficient L D|) ^ 2 / 2) *
        Real.exp (∑ D ∈ population G R, |infiniteCenteredCoefficient L D|) := by
  classical
  let FN := F.filter fun I ↦ infiniteCenteredCoefficient L I ≠ 0
  have heq : (∑ I ∈ FN, |infiniteCenteredCoefficient L I|) =
      ∑ I ∈ F, |infiniteCenteredCoefficient L I| := by
    rw [show FN = F.filter (fun I ↦ infiniteCenteredCoefficient L I ≠ 0) from rfl, sum_filter]
    apply sum_congr rfl
    intro I _hI
    by_cases hc : infiniteCenteredCoefficient L I = 0 <;> simp [hc]
  rw [← heq]
  apply FinitePolymerTail.covered_bound FN (population G R)
    (fun I ↦ |infiniteCenteredCoefficient L I|) (fun C ↦ |infiniteCenteredCoefficient L C|)
    (fun C ↦ abs_nonneg _)
  intro I hI
  obtain ⟨hIF, hc⟩ := mem_filter.mp hI
  obtain ⟨hIG, hnonempty, hcap, hconn⟩ := hF I hIF
  refine ⟨blocks L I, ?_, union_blocks L I, nonconnected_card L I hnonempty hconn,
    (absolute_factor L hL I).le⟩
  intro C hC
  have hCI := block_subset L I C hC
  exact mem_filter.mpr ⟨mem_powerset.mpr (hCI.trans hIG),
    nonzero_block_card L hL I C hc hC, (card_le_card hCI).trans hcap⟩

end PaperP1.BoundedComponentActivity
