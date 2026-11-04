module

public import PaperP1.Probability.PositionalPoissonPolynomialMoments
public import PaperP1.Asymptotics.PositionalCompoundDeletionRate

/-! # Uniformly bounded moments of the actual independent erased background -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalBackgroundMoments

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw
  PaperP1.CompletedPositionalLaw PaperP1.PositionalCountProjection

theorem uniform_bound (r : ℕ) (C : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      let E := GoodEdgeCompression.goodEdges H N L
      let U := PositionalMarkedPairExpansion.background (dyadicBlock N) E
        (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
      PositivePositionalConvolution.IsProbability U ∧
      Summable (fun v ↦ coeff v U * (1 + (totalCount v : ℝ)) ^ r) ∧
      (∑' v, coeff v U * (1 + (totalCount v : ℝ)) ^ r) ≤ B := by
  let M : ℝ := (2 : ℝ) ^ C
  obtain ⟨B, hB, hmoment⟩ := PositionalPoissonPolynomialMoments.uniform_bound (ι := ℕ) M r
  obtain ⟨NP, _hNP, hp⟩ := WeakPairIncidence.full_single_rates_positive C
  refine ⟨B, hB, 3 + NP, by omega, ?_⟩
  intro N hN L hband H
  dsimp only
  let E := GoodEdgeCompression.goodEdges H N L
  let t := fun x ↦ (2 ^ L : ℝ)⁻¹ - PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x
  have ht0 (x : ℕ) : 0 ≤ t x := (hp N (by omega) L hband H x).le
  have ht (x : ℕ) : t x ≤ (2 ^ L : ℝ)⁻¹ := by
    apply sub_le_self
    unfold PositionalCompoundPoisson.incidence
    apply sum_nonneg
    intro e _he
    split_ifs
    · exact infiniteJointMoment_nonneg L e
    · exact le_rfl
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmean : (∑ x ∈ dyadicBlock N, t x) ≤ M := by
    calc
      _ ≤ ∑ _x ∈ dyadicBlock N, (2 ^ L : ℝ)⁻¹ := sum_le_sum (fun x _hx ↦ ht x)
      _ = (N : ℝ) * (2 ^ L : ℝ)⁻¹ := by rw [sum_const, nsmul_eq_mul, dyadicBlock_card]
      _ ≤ (N : ℝ) * ((2 : ℝ) ^ C / N) := mul_le_mul_of_nonneg_left
        (LocalRigidityConsequences.nominal_marginal_bound (by omega) hband) hn.le
      _ = M := by dsimp [M]; field_simp
  exact ⟨PositionalPoissonObservables.poisson_isProbability _ t (fun x _hx ↦ ht0 x),
    hmoment (dyadicBlock N) t (fun x _hx ↦ ht0 x) hmean⟩

end PaperP1.PositionalBackgroundMoments
