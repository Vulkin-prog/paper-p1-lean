module

public import PaperP1.Asymptotics.FixedDependentJointMass
public import PaperP1.Asymptotics.DependentProductMass
public import PaperP1.Model.AbsoluteActivityDecomposition

/-! # Full actual absolute centered activity has rate2/3 throughout every prescribed bounded order range -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedAbsoluteActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.HeterogeneousDirectMaximum PaperP1.DependentFamilySeeds

theorem uniform_range (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r : ℕ, 1 ≤ r → r ≤ R →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ I ∈ G.powersetCard r, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-2 / 3 + ε) := by
  classical
  let M : ℝ := 2 * (2 : ℝ) ^ C
  let B := fun r : ℕ ↦ (2 : ℝ) ^ r +
    ∑ s ∈ range (r + 1), M ^ (r - s) / ((r - s).factorial : ℝ)
  obtain ⟨ND, _hND, hd⟩ := FixedDependentJointMass.uniform_range R C (ε / 2) (by positivity)
  have hproduct (i : Fin (R + 1)) := DependentProductMass.uniform_mass i.val C (ε / 2) (by positivity)
  choose NP _hNP hp using hproduct
  have hfactor (i : Fin (R + 1)) := HalfCountSchedule.factor_absorption (B i.val)
    (-2 / 3 + ε / 2) (ε / 2) (by positivity)
  choose NF hf using hfactor
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨10 + ND + NM + NG + univ.sup NP + univ.sup NF, by omega, ?_⟩
  intro N hN L hband r hr1 hrR G hG
  let i : Fin (R + 1) := ⟨r, by omega⟩
  have hNPi : NP i ≤ univ.sup NP := le_sup (f := NP) (mem_univ i)
  have hNFi : NF i ≤ univ.sup NF := le_sup (f := NF) (mem_univ i)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hμ : 0 ≤ actualMean G L := sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hμM : actualMean G L ≤ M := by
    calc
      _ ≤ actualMean (dyadicBlock N) L := sum_le_sum_of_subset_of_nonneg hG
        (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = CountObservables.countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment Subset.rfl
      _ ≤ _ := (hm N (by omega) L hband).2
  let T := (N : ℝ) ^ (-2 / 3 + ε / 2)
  have hT : 0 ≤ T := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hprod : DependentProductMass.mass G L r ≤ T := (hp i N (by omega) L hband G hG).trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only []))
  have hdep (s : ℕ) (hs : s ∈ range (r + 1)) : dependentMass G L s ≤ T := by
    by_cases hsmall : s ≤ 1
    · rw [dependentMass, DependentSeedCover.low_card_empty G L s hsmall, sum_empty]
      exact hT
    · exact hd N (by omega) L hband s (by omega)
        (by have h := mem_range.mp hs; omega) G hG
  have hsum : (∑ s ∈ range (r + 1), dependentMass G L s *
      (actualMean G L ^ (r - s) / ((r - s).factorial : ℝ))) ≤
      T * ∑ s ∈ range (r + 1), M ^ (r - s) / ((r - s).factorial : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro s hs
    exact mul_le_mul (hdep s hs)
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hμ hμM (r - s)) (Nat.cast_nonneg _))
      (div_nonneg (pow_nonneg hμ _) (Nat.cast_nonneg _)) hT
  calc
    _ ≤ (2 : ℝ) ^ r * DependentProductMass.mass G L r +
        ∑ s ∈ range (r + 1), dependentMass G L s *
          (actualMean G L ^ (r - s) / ((r - s).factorial : ℝ)) :=
      AbsoluteActivityDecomposition.absolute_power_bound G L r hL hr1
    _ ≤ (2 : ℝ) ^ r * T + T * ∑ s ∈ range (r + 1), M ^ (r - s) / ((r - s).factorial : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hprod (by positivity)) hsum
    _ = B r * T := by dsimp [B]; ring
    _ ≤ _ := by
      convert hf i N (by omega) using 1
      congr 1
      ring

end PaperP1.FixedAbsoluteActivity
