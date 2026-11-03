module

public import PaperP1.Asymptotics.ConnectedIndependent256Budget
public import PaperP1.Model.RelationCoreActivityPeeling
public import PaperP1.Asymptotics.CriticalPairKernelPowers

/-! # Large connected families below compatible nullity L/60 have power 83/60 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LowCompatibleNullityTail

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

theorem uniform_bound (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 256 ≤ I.card ∧ Connected L I ∧
        (runCompatibleNullity L I : ℝ) ≤ (L : ℝ) / 60) →
      (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-83 / 60 + ε) := by
  obtain ⟨NI, _hNI, hi⟩ := PaperP1.ConnectedIndependent256Budget.uniform_bound
    (2 * u) C (ε / 2) (by positivity) (by positivity)
  obtain ⟨NP, hp⟩ := PaperP1.CriticalPairKernelPowers.power_of_rank
    C (1 / 60) 0 (ε / 2) (by norm_num) (by positivity)
  obtain ⟨NF, hf⟩ := PaperP1.SaturationDegrees.finite_conditions C 14 (by norm_num)
  refine ⟨10 + NI + NP + NF, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB : 2 ≤ L + 1 := (hf N (by omega) L hband).2.1
  have hL : 0 < L := by omega
  have hamp (I : Finset ℕ) (hI : I ∈ F) : (2 ^ runCompatibleNullity L I : ℝ) ≤
      (N : ℝ) ^ ((1 / 60 : ℝ) + ε / 2) := by
    apply hp N (by omega) L (runCompatibleNullity L I) hband
    have hcap := (hF I hI).2.2.2
    have hεL : 0 ≤ ε * (L : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg L)
    push_cast
    nlinarith only [hcap, hε, hεL]
  have hpoint (I : Finset ℕ) (hI : I ∈ F) :
      u ^ I.card * |infiniteCenteredCoefficient L I| ≤
        (N : ℝ) ^ ((1 / 60 : ℝ) + ε / 2) * ∏ x ∈ I, (2 * u) * infiniteMarginal x L := by
    have hmajor := PaperP1.RelationCoreActivityPeeling.compatible_majorant L hL I
    have hnonneg : 0 ≤ (2 ^ I.card : ℝ) * ∏ x ∈ I, infiniteMarginal x L :=
      mul_nonneg (by positivity)
        (prod_nonneg fun x _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    calc
      _ ≤ u ^ I.card * ((2 ^ I.card : ℝ) * (∏ x ∈ I, infiniteMarginal x L) *
          (2 ^ runCompatibleNullity L I : ℝ)) := mul_le_mul_of_nonneg_left hmajor (pow_nonneg hu.le _)
      _ ≤ u ^ I.card * ((2 ^ I.card : ℝ) * (∏ x ∈ I, infiniteMarginal x L) *
          (N : ℝ) ^ ((1 / 60 : ℝ) + ε / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hamp I hI) hnonneg) (pow_nonneg hu.le _)
      _ = _ := by rw [prod_mul_distrib, prod_const, mul_pow]; ring
  have hindep := hi N (by omega) L hband F (by
    intro I hI
    exact ⟨(hF I hI).1, (hF I hI).2.1, (hF I hI).2.2.1⟩)
  calc
    _ ≤ ∑ I ∈ F, (N : ℝ) ^ ((1 / 60 : ℝ) + ε / 2) *
        ∏ x ∈ I, (2 * u) * infiniteMarginal x L := sum_le_sum hpoint
    _ = (N : ℝ) ^ ((1 / 60 : ℝ) + ε / 2) *
        ∑ I ∈ F, ∏ x ∈ I, (2 * u) * infiniteMarginal x L := by rw [← mul_sum]
    _ ≤ (N : ℝ) ^ ((1 / 60 : ℝ) + ε / 2) * (N : ℝ) ^ (-7 / 5 + ε / 2) :=
      mul_le_mul_of_nonneg_left hindep (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.LowCompatibleNullityTail
