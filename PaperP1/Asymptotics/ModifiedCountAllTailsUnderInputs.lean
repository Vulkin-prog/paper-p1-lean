module

public import PaperP1.Asymptotics.RetainedExceptionalEventUnderInputs
public import PaperP1.Model.OriginalCountLawCoupling
public import PaperP1.Model.RetainedModifiedBounds

/-! # Companion T19.3 with all orders and all exponential parameters after one common threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ModifiedCountAllTailsUnderInputs

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.RetainedActiveCount PaperP1.RetainedCountCylinder PaperP1.RetainedExceptionalEventUnderInputs

theorem uniform_restored_totalVariation (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (ε / 2) → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L)
        (RetainedModifiedLaw.law (8 * (L + 1) : ℕ) N L (RegularStarts.regularStarts N L)) ≤
          (N : ℝ) ^ (-4 / 5 + ε) ∧
      badProbability (8 * (L + 1) : ℕ) N L (RegularStarts.regularStarts N L) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨p, hp⟩ := uniform_badProbability C (ε / 2) (by positivity)
  obtain ⟨ND, hd⟩ := RegularSetAsymptotic.discarded_activity_critical C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (1 + 2 * (2 : ℝ) ^ C)
    (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NB, _hNB, hb⟩ := hp hgeo
  refine ⟨10 + NB + ND + NG + NF, by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hbad := hb N (by omega) L hband _ (RegularStarts.regularStarts_subset N L)
  have hpower : (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [])
  have hdel := (hd N (by omega) L hL hband).trans
    (mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ 2 * (2 : ℝ) ^ C))
  have htv := OriginalCountLawCoupling.restore_modified (8 * (L + 1) : ℕ) N L
  refine ⟨?_, hbad.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε]))⟩
  calc
    _ ≤ (1 + 2 * (2 : ℝ) ^ C) * (N : ℝ) ^ (-4 / 5 + ε / 2) := by linarith only [htv, hdel, hbad]
    _ ≤ (N : ℝ) ^ ((-4 / 5 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem companion_T19_3 (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (ε / 2) → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      let G := RegularStarts.regularStarts N L
      let H : ℝ := (8 * (L + 1) : ℕ)
      let μ := MaximumDirectActive.mean G L
      AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L)
        (RetainedModifiedLaw.law H N L G) ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
      badProbability H N L G ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
      ∀ k r : ℕ, 1 ≤ k → 1 ≤ r → ∀ s : ℝ, 1 ≤ s →
        infiniteRademacherMeasure.real {ω | k ≤ infiniteStartCount G L ω} ≤
          μ ^ (k - 1) / (k - 1).factorial + badProbability H N L G ∧
        infiniteRademacherMeasure.real {ω | k ≤ modified H N L G ω} ≤ μ ^ (k - 1) / (k - 1).factorial ∧
        (∫ ω, s ^ modified H N L G ω ∂infiniteRademacherMeasure) ≤
          s * (1 + (2 ^ L : ℝ)⁻¹ * (s - 1)) ^ G.card ∧
        (∫ ω, s ^ modified H N L G ω ∂infiniteRademacherMeasure) ≤ s * Real.exp ((s - 1) * μ) ∧
        (∫ ω, ((modified H N L G ω).descFactorial r : ℝ) ∂infiniteRademacherMeasure) ≤
          μ ^ r + (r : ℝ) * μ ^ (r - 1) := by
  obtain ⟨p, hp⟩ := uniform_restored_totalVariation C ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨N₀, _hN₀, h⟩ := hp hgeo
  refine ⟨10 + N₀ + NG, by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  refine ⟨(h N (by omega) L hband).1, (h N (by omega) L hband).2, ?_⟩
  intro k r hk hr s hs
  exact RetainedModifiedBounds.companion_T19_3_bounds (8 * (L + 1) : ℕ) (by omega : 2 ≤ N) hL
    (RegularStarts.regularStarts N L) Subset.rfl k r hk hr s hs

end PaperP1.ModifiedCountAllTailsUnderInputs
