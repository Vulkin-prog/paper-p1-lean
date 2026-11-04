module

public import PaperP1.Probability.PositionalPoissonAccidents
public import PaperP1.Probability.PositionalBackgroundDeletion
public import PaperP1.Asymptotics.GoodEdgeAccidentalMass
public import PaperP1.Asymptotics.WeakPairIncidence

/-! # Accidental good edges and deletion in the actual independent background

All bounds are unconditional and uniform over the real private-prime threshold.
The compound-field comparison still requires its marked pair arrivals.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalPoissonAccidentRate

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw
  PaperP1.CompletedPositionalLaw PaperP1.PositionalPairDeletion

theorem uniform_any_active (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ, ∀ r : ℕ → ℝ,
      (∀ x ∈ dyadicBlock N, 0 ≤ r x ∧ r x ≤ (2 ^ L : ℝ)⁻¹) →
      let U := PositionalBernoulliProducts.poisson (dyadicBlock N) r
      let E := GoodEdgeCompression.goodEdges H N L
      Summable (fun v : Configuration ℕ ↦ if (activeEdges E v).Nonempty then coeff v U else 0) ∧
      (∑' v : Configuration ℕ, if (activeEdges E v).Nonempty then coeff v U else 0) ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := GoodEdgeAccidentalMass.uniform_bound C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband H r hr
  have hh := PositionalPoissonAccidents.any_active_bound (dyadicBlock N) r
    (fun x hx ↦ (hr x hx).1) (GoodEdgeCompression.goodEdges H N L) (fun e he ↦
      ⟨(RetainedGoodEdges.good_pair_regular (by omega) e he).trans
        (RegularStarts.regularStarts_subset N L), RetainedGoodEdges.good_pair_card H N L e he⟩)
  exact ⟨hh.1, hh.2.trans (h N hN L hband H r hr)⟩

theorem uniform_background (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      let E := GoodEdgeCompression.goodEdges H N L
      let r := fun x ↦ (2 ^ L : ℝ)⁻¹ - PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x
      let U := PositionalBernoulliProducts.poisson (dyadicBlock N) r
      PositivePositionalConvolution.IsProbability U ∧
      (∑' v : Configuration ℕ, if (activeEdges E v).Nonempty then coeff v U else 0) ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NA, _hNA, ha⟩ := uniform_any_active C ε hε
  obtain ⟨NP, _hNP, hp⟩ := WeakPairIncidence.full_single_rates_positive C
  refine ⟨3 + NA + NP, by omega, ?_⟩
  intro N hN L hband H
  dsimp only
  let E := GoodEdgeCompression.goodEdges H N L
  let r := fun x ↦ (2 ^ L : ℝ)⁻¹ - PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x
  have hr (x : ℕ) (_hx : x ∈ dyadicBlock N) : 0 ≤ r x ∧ r x ≤ (2 ^ L : ℝ)⁻¹ := by
    have hi : 0 ≤ PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x := by
      unfold PositionalCompoundPoisson.incidence
      apply sum_nonneg
      intro e _he
      split_ifs
      · exact infiniteJointMoment_nonneg L e
      · exact le_rfl
    exact ⟨(hp N (by omega) L hband H x).le, sub_le_self _ hi⟩
  exact ⟨PositionalPoissonObservables.poisson_isProbability _ r (fun x hx ↦ (hr x hx).1),
    (ha N (by omega) L hband H r hr).2⟩

theorem uniform_background_deletion (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      let E := GoodEdgeCompression.goodEdges H N L
      let r := fun x ↦ (2 ^ L : ℝ)⁻¹ - PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x
      let U := PositionalBernoulliProducts.poisson (dyadicBlock N) r
      ‖PositionalDeletionKernels.once E U - U‖ ≤ (N : ℝ) ^ (-1 + ε) ∧
      ‖PositionalDeletionKernels.isolated E U - U‖ ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NB, _hNB, hb⟩ := uniform_background C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NB + NF, by omega, ?_⟩
  intro N hN L hband H
  dsimp only
  let E := GoodEdgeCompression.goodEdges H N L
  let r := fun x ↦ (2 ^ L : ℝ)⁻¹ - PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x
  let U := PositionalBernoulliProducts.poisson (dyadicBlock N) r
  have hh := hb N (by omega) L hband H
  have hmass : 2 * (∑' v : Configuration ℕ,
      if (activeEdges E v).Nonempty then coeff v U else 0) ≤ (N : ℝ) ^ (-1 + ε) := by
    have hbnd := mul_le_mul_of_nonneg_left hh.2 (by norm_num : (0 : ℝ) ≤ 2)
    have hfactor : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
      convert hf N (by omega) using 1
      congr 1
      ring
    exact hbnd.trans hfactor
  exact ⟨(PositionalBackgroundDeletion.once_event_bound E U hh.1.1).trans hmass,
    (PositionalBackgroundDeletion.isolated_event_bound E U hh.1.1).trans hmass⟩

end PaperP1.PositionalPoissonAccidentRate
