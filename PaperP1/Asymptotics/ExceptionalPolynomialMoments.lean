module

public import PaperP1.Model.ActiveSetExceptionalMoment
public import PaperP1.Asymptotics.SubpowerFixedCountMoments
public import PaperP1.Asymptotics.RetainedExceptionalEvent
public import PaperP1.Model.RegularMomentTransfer

/-! # One internally proved exceptional event controls every fixed polynomial degree, using unconditional subpower moments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExceptionalPolynomialMoments

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RetainedExceptionalEvent

theorem uniform_fixed (C : ℝ) :
    ∀ j : ℕ,
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ∀ f : Finset ℕ → ℝ, (∀ A ⊆ G, 0 ≤ f A ∧ f A ≤ (A.card : ℝ) ^ j) →
        ActiveSetExceptionalMoment.value (8 * (L + 1) : ℕ) N L G f ≤ (N : ℝ) ^ (-83 / 120 : ℝ) := by
  obtain ⟨NB, _hNB, hb⟩ := uniform_badProbability C (1 / 120) (by norm_num)
  intro j
  obtain ⟨NM, _hNM, hm⟩ := SubpowerFixedCountMoments.uniform_ordinary (8 * j) C (1 / 120) (by norm_num)
  refine ⟨10 + NB + NM, by omega, ?_⟩
  intro N hN L hband G hG f hbound
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM0 := RegularMomentTransfer.countMoment_nonneg (L := L) hG (8 * j)
  have hM := Real.rpow_le_rpow hM0 (hm N (by omega) L hband G hG) (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hB := Real.rpow_le_rpow (by exact ENNReal.toReal_nonneg)
    (hb N (by omega) L hband G hG) (by norm_num : (0 : ℝ) ≤ 7 / 8)
  have hprod := mul_le_mul hM hB (Real.rpow_nonneg (by exact ENNReal.toReal_nonneg) _)
    (Real.rpow_nonneg (Real.rpow_nonneg hnpos.le _) _)
  calc
    _ ≤ CountObservables.countMoment G L (8 * j) ^ (1 / 8 : ℝ) *
        RetainedCountCylinder.badProbability (8 * (L + 1) : ℕ) N L G ^ (7 / 8 : ℝ) :=
      ActiveSetExceptionalMoment.eighth_bound _ N L G f j hbound
    _ ≤ ((N : ℝ) ^ (1 / 120 : ℝ)) ^ (1 / 8 : ℝ) *
        ((N : ℝ) ^ (-4 / 5 + 1 / 120 : ℝ)) ^ (7 / 8 : ℝ) := hprod
    _ = _ := by
      rw [← Real.rpow_mul hnpos.le, ← Real.rpow_mul hnpos.le, ← Real.rpow_add hnpos]
      congr 1
      norm_num

end PaperP1.ExceptionalPolynomialMoments
