module

public import PaperP1.Probability.PositionalInsertedPairCoupling
public import PaperP1.Asymptotics.GoodEdgeTouchingMassRate
public import PaperP1.Asymptotics.PositionalPoissonAccidentRate

/-! # Recovering an inserted good pair from a Poisson background, uniformly

The touching-site cost has a half-power bound without a graph-degree input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalInsertedPairRate

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw
  PaperP1.FiniteConvolutionAlgebra PaperP1.CompletedPositionalLaw
  PaperP1.PositionalPairDeletion PaperP1.PositionalDeletionKernels

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ, ∀ r : ℕ → ℝ,
      (∀ x, 0 ≤ r x) → (∀ x ∈ dyadicBlock N, r x ≤ (2 ^ L : ℝ)⁻¹) →
      ∀ e ∈ GoodEdgeCompression.goodEdges H N L,
      let E := GoodEdgeCompression.goodEdges H N L
      let U := PositionalBernoulliProducts.poisson (dyadicBlock N) r
      ‖once E (ofFinite (atom (edgeVector e)) * U) - U‖ ≤ (N : ℝ) ^ (-1 / 2 + ε) ∧
      ‖isolated E (ofFinite (atom (edgeVector e)) * U) - U‖ ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨NA, _hNA, ha⟩ := GoodEdgeAccidentalMass.uniform_bound C (ε / 4) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := GoodEdgeTouchingMassRate.uniform_bound C (ε / 4) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (-1 / 2 + ε / 4) (3 * ε / 4) (by positivity)
  refine ⟨3 + NA + NT + NF, by omega, ?_⟩
  intro N hN L hband H r hr0 hr e he
  dsimp only
  let E := GoodEdgeCompression.goodEdges H N L
  let U := PositionalBernoulliProducts.poisson (dyadicBlock N) r
  let P := (N : ℝ) ^ (-1 / 2 + ε / 4)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hE : ∀ f ∈ E, f ⊆ dyadicBlock N ∧ f.card = 2 := by
    intro f hfE
    exact ⟨(RetainedGoodEdges.good_pair_regular (by omega) f hfE).trans
      (RegularStarts.regularStarts_subset N L), RetainedGoodEdges.good_pair_card H N L f hfE⟩
  have hA : (∑ f ∈ E, ∏ x ∈ f, r x) ≤ P :=
    (ha N (by omega) L hband H r (fun x hx ↦ ⟨hr0 x, hr x hx⟩)).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [] :
        (-1 : ℝ) + ε / 4 ≤ -1 / 2 + ε / 4))
  have hT : (∑ x ∈ PositionalInsertedPair.touchingVertices E e, r x) ≤ P :=
    ht N (by omega) L hband H r hr0
      (fun x hx ↦ hr x (RegularStarts.regularStarts_subset N L hx)) e he
  have hfactor : 4 * P ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hmass : 2 * ((∑ f ∈ E, ∏ x ∈ f, r x) +
      ∑ x ∈ PositionalInsertedPair.touchingVertices E e, r x) ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
    linarith only [hA, hT, hfactor]
  exact ⟨(PositionalInsertedPairCoupling.once_poisson_bound (dyadicBlock N) r
      (fun x _hx ↦ hr0 x) E hE e he).trans hmass,
    (PositionalInsertedPairCoupling.isolated_poisson_bound (dyadicBlock N) r
      (fun x _hx ↦ hr0 x) E hE e he).trans hmass⟩

theorem uniform_background (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      let E := GoodEdgeCompression.goodEdges H N L
      let r := fun x ↦ (2 ^ L : ℝ)⁻¹ - PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x
      let U := PositionalBernoulliProducts.poisson (dyadicBlock N) r
      ∀ e ∈ E,
      ‖once E (ofFinite (atom (edgeVector e)) * U) - U‖ ≤ (N : ℝ) ^ (-1 / 2 + ε) ∧
      ‖isolated E (ofFinite (atom (edgeVector e)) * U) - U‖ ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨NB, _hNB, hb⟩ := uniform_bound C ε hε
  obtain ⟨NP, _hNP, hp⟩ := WeakPairIncidence.full_single_rates_positive C
  refine ⟨3 + NB + NP, by omega, ?_⟩
  intro N hN L hband H
  dsimp only
  let E := GoodEdgeCompression.goodEdges H N L
  let r := fun x ↦ (2 ^ L : ℝ)⁻¹ - PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x
  have hr0 (x : ℕ) : 0 ≤ r x := (hp N (by omega) L hband H x).le
  have hr (x : ℕ) (_hx : x ∈ dyadicBlock N) : r x ≤ (2 ^ L : ℝ)⁻¹ := by
    apply sub_le_self
    unfold PositionalCompoundPoisson.incidence
    apply sum_nonneg
    intro e _he
    split_ifs
    · exact infiniteJointMoment_nonneg L e
    · exact le_rfl
  exact hb N (by omega) L hband H r hr0 hr

end PaperP1.PositionalInsertedPairRate
