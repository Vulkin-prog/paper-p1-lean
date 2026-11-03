module

public import PaperP1.Asymptotics.ConnectedReductionToTriplesUnderInputs

/-! # Finite weighted connected activity with the actual third activity left symbolic -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleControlledFixedActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.ConnectedReductionToTriplesUnderInputs

theorem uniform_weighted (R : ℕ) (u C ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε) :
    ∃ p : Parameters R, Hypotheses p (ε / 2) → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ G ∧ 3 ≤ I.card ∧ I.card ≤ R ∧ Connected L I) →
      (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤
        (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L (G.powersetCard 3) +
        (N : ℝ) ^ (-4 / 3 + ε) := by
  classical
  obtain ⟨p, hp⟩ := ConnectedReductionToTriplesUnderInputs.uniform_range R C (ε / 2) (by positivity)
  let B := ∑ r ∈ Icc 3 R, u ^ r
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption B 0 (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NA, _hNA, ha⟩ := hp hgeo
  refine ⟨10 + NF + NA, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let A3 := CompatibleActivitySplit.absolute L (G.powersetCard 3)
  let P := (N : ℝ) ^ (ε / 2) * A3 + (N : ℝ) ^ (-4 / 3 + ε / 2)
  let Fi := fun r : ℕ ↦ F.filter fun I ↦ I.card = r
  have hA3 : 0 ≤ A3 := sum_nonneg fun I _ ↦ abs_nonneg _
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hcell (r : ℕ) (hr : r ∈ Icc 3 R) :
      (∑ I ∈ Fi r, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ u ^ r * P := by
    have hsub : Fi r ⊆ connectedFamilies G L r := by
      intro I hI
      obtain ⟨hIF, hcard⟩ := mem_filter.mp hI
      have hi := hF I hIF
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hi.1, hcard⟩, hi.2.2.2⟩
    have hbound := (ha N (by omega) L hband r (mem_Icc.mp hr).1 (mem_Icc.mp hr).2 G hG (Fi r) hsub).1
    calc
      _ = u ^ r * ∑ I ∈ Fi r, |infiniteCenteredCoefficient L I| := by
        rw [mul_sum]
        apply sum_congr rfl
        intro I hI
        rw [(mem_filter.mp hI).2]
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound (pow_nonneg hu _)
  have hsplit := sum_fiberwise_of_maps_to (s := F) (t := Icc 3 R)
    (g := fun I : Finset ℕ ↦ I.card) (fun I hI ↦ mem_Icc.mpr ⟨(hF I hI).2.1, (hF I hI).2.2.1⟩)
    (fun I ↦ u ^ I.card * |infiniteCenteredCoefficient L I|)
  have hconstant : B ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using hf N (by omega)
  calc
    _ = ∑ r ∈ Icc 3 R, ∑ I ∈ Fi r, u ^ I.card * |infiniteCenteredCoefficient L I| := hsplit.symm
    _ ≤ ∑ r ∈ Icc 3 R, u ^ r * P := sum_le_sum hcell
    _ = B * P := (sum_mul ..).symm
    _ ≤ (N : ℝ) ^ (ε / 2) * P := mul_le_mul_of_nonneg_right hconstant hP
    _ = _ := by
      dsimp only [P]
      rw [mul_add, ← mul_assoc, ← Real.rpow_add hn, add_halves, ← Real.rpow_add hn]
      congr 1
      congr 1
      ring

end PaperP1.TripleControlledFixedActivity
