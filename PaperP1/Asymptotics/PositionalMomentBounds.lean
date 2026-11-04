module

public import PaperP1.Model.PositionalCountMoments
public import PaperP1.Probability.PositionalReferenceMoments
public import PaperP1.Asymptotics.SubpowerFixedCountMoments
public import PaperP1.Asymptotics.WeakPairIncidence

/-! # Original moments are subpolynomial; the full reference moments are bounded

Every polynomial degree is fixed before its critical threshold. These moment
bounds are unconditional and retain all positions of the original dyadic grid.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalMomentBounds

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw
  PaperP1.PositionalCountProjection PaperP1.CompletedPositionalLaw

theorem uniform_original (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      Summable (fun v : Configuration ℕ ↦ (PositionalStoppedLaw.actualLaw G L).coeff v *
        (1 + (totalCount v : ℝ)) ^ r) ∧
      (∑' v : Configuration ℕ, (PositionalStoppedLaw.actualLaw G L).coeff v *
        (1 + (totalCount v : ℝ)) ^ r) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NM, _hNM, hm⟩ := SubpowerFixedCountMoments.uniform_ordinary r C (ε / 2) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption
    (2 * (2 : ℝ) ^ r) (ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NM + NA, by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlarge : 1 ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hn1 (by positivity)
  have hh := PositionalCountMoments.weighted_moment_bound G L r
  refine ⟨hh.1, hh.2.trans ?_⟩
  calc
    _ ≤ (2 * (2 : ℝ) ^ r) * (N : ℝ) ^ (ε / 2) := by
      have hmoment := hm N (by omega) L hband G hG
      have hinside : 1 + CountObservables.countMoment G L r ≤ 2 * (N : ℝ) ^ (ε / 2) :=
        by linarith only [hmoment, hlarge]
      nlinarith only [mul_le_mul_of_nonneg_left hinside (by positivity : 0 ≤ (2 : ℝ) ^ r)]
    _ ≤ (N : ℝ) ^ (ε / 2 + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_reference (r : ℕ) (C : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      let T := PositionalCompoundPoisson.target (dyadicBlock N)
        (GoodEdgeCompression.goodEdges H N L) (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
      Summable (fun v ↦ coeff v T * (1 + (totalCount v : ℝ)) ^ r) ∧
      (∑' v, coeff v T * (1 + (totalCount v : ℝ)) ^ r) ≤ B := by
  let M : ℝ := (2 : ℝ) ^ C
  obtain ⟨B, hB, hmoment⟩ := PositionalReferenceMoments.uniform_bound (ι := ℕ) M r
  obtain ⟨NP, _hNP, hp⟩ := WeakPairIncidence.full_single_rates_positive C
  refine ⟨B, hB, 3 + NP, by omega, ?_⟩
  intro N hN L hband H
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmean : (∑ _x ∈ dyadicBlock N, (2 ^ L : ℝ)⁻¹) ≤ M := by
    calc
      _ = (N : ℝ) * (2 ^ L : ℝ)⁻¹ := by rw [sum_const, nsmul_eq_mul, dyadicBlock_card]
      _ ≤ (N : ℝ) * ((2 : ℝ) ^ C / N) := mul_le_mul_of_nonneg_left
        (LocalRigidityConsequences.nominal_marginal_bound (by omega) hband) hn.le
      _ = M := by dsimp [M]; field_simp
  exact hmoment (dyadicBlock N) (GoodEdgeCompression.goodEdges H N L)
    (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
    (fun e he ↦ ⟨(RetainedGoodEdges.good_pair_regular (by omega) e he).trans
      (RegularStarts.regularStarts_subset N L), RetainedGoodEdges.good_pair_card H N L e he⟩)
    (fun x _hx ↦ (hp N (by omega) L hband H x).le)
    (fun e _he ↦ infiniteJointMoment_nonneg L e) hmean

end PaperP1.PositionalMomentBounds
