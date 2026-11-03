module

public import PaperP1.Model.IncidentPairMass
public import PaperP1.Asymptotics.IndependentTargetMass
public import PaperP1.Asymptotics.CriticalPairKernelPowers
public import PaperP1.Model.RetainedGoodEdges
public import PaperP1.Model.RetainedReferenceTheorem

/-! # Strict positivity of the original single Poisson rates without degree bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeakPairIncidence

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ E : Finset (Finset ℕ),
      (∀ e ∈ E, e ⊆ G ∧ e.card = 2 ∧ 0 < runRelativeNullity L e ∧
        (runRelativeNullity L e : ℝ) ≤ (L : ℝ) / 3 + 1) →
      ∀ x ∈ G, PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x ≤
        infiniteMarginal x L * (N : ℝ) ^ (-1 / 12 : ℝ) := by
  obtain ⟨NR, hr⟩ := CriticalPairKernelPowers.power_of_rank C (1 / 3) 1 (1 / 24) (by norm_num) (by norm_num)
  obtain ⟨NT, ht⟩ := IndependentTargetMass.uniform_mass 1 C (1 / 24) (by norm_num)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NR + NT + NG, by omega, ?_⟩
  intro N hN L hband G hG E hE x hx
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  let K := (N : ℝ) ^ ((1 / 3 : ℝ) + 1 / 24)
  have hfinite := IncidentPairMass.finite_bound G L hL E K (Real.rpow_nonneg hn.le _) (by
    intro e he
    obtain ⟨heG, hcard, hpos, hdim⟩ := hE e he
    refine ⟨heG, hcard, hpos, hr N (by omega) L (runRelativeNullity L e) hband ?_⟩
    push_cast
    nlinarith only [hdim, Nat.cast_nonneg (α := ℝ) L]) x
  have htargets := ht N (by omega) L G {x} hband hG (singleton_subset_iff.mpr hx) (card_singleton x)
  calc
    _ ≤ (infiniteMarginal x L * K) * ∑ y ∈ WindowTargetHosts.targets G L {x}, infiniteMarginal y L := hfinite
    _ ≤ (infiniteMarginal x L * K) * (N : ℝ) ^ (-(1 : ℝ) / 2 + 1 / 24) :=
      mul_le_mul_of_nonneg_left htargets
        (mul_nonneg (MissingBlockProbabilities.infiniteMarginal_nonneg x L) (Real.rpow_nonneg hn.le _))
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 1
      norm_num

theorem good_single_rates_positive (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      ∀ x ∈ RegularStarts.regularStarts N L,
      0 < infiniteMarginal x L -
        PositionalCompoundPoisson.incidence (GoodEdgeCompression.goodEdges H N L) (infiniteJointMoment L) x := by
  obtain ⟨NI, _hNI, hi⟩ := uniform_bound C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NI + NG, by omega, ?_⟩
  intro N hN L hband H x hx
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  have hh := hi N (by omega) L hband (RegularStarts.regularStarts N L)
    (RegularStarts.regularStarts_subset N L) (GoodEdgeCompression.goodEdges H N L) (by
      intro e he
      exact ⟨RetainedGoodEdges.good_pair_regular (by omega) e he, RetainedGoodEdges.good_pair_card H N L e he,
        RetainedGoodEdges.good_pair_positive H N L e he, RetainedGoodEdges.good_pair_nullity_le (by omega) e he⟩) x hx
  have hpx : 0 < infiniteMarginal x L := by
    rw [RetainedReferenceTheorem.ground_marginal (by omega) hL x hx]
    positivity
  have hn1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hsmall : (N : ℝ) ^ (-1 / 12 : ℝ) < 1 := by
    have hpow := Real.rpow_lt_rpow_of_exponent_lt hn1 (by norm_num : (-1 / 12 : ℝ) < 0)
    simpa only [Real.rpow_zero] using hpow
  have hstrict := hh.trans_lt ((mul_lt_mul_of_pos_left hsmall hpx).trans_eq (mul_one _))
  exact sub_pos.mpr hstrict

theorem good_target_isProbability (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      PositivePositionalConvolution.IsProbability
        (PositionalCompoundPoisson.target (RegularStarts.regularStarts N L) (GoodEdgeCompression.goodEdges H N L)
          (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L)) := by
  obtain ⟨N₀, hN₀, h⟩ := good_single_rates_positive C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband H
  exact PositionalCompoundPoisson.target_isProbability _ _ _ _
    (fun x hx ↦ (h N hN L hband H x hx).le) (fun e _ ↦ infiniteJointMoment_nonneg L e)

theorem full_single_rates_positive (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ, ∀ x : ℕ,
      0 < (2 ^ L : ℝ)⁻¹ -
        PositionalCompoundPoisson.incidence (GoodEdgeCompression.goodEdges H N L) (infiniteJointMoment L) x := by
  obtain ⟨NP, _hNP, hp⟩ := good_single_rates_positive C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NP + NG, by omega, ?_⟩
  intro N hN L hband H x
  classical
  by_cases hx : x ∈ RegularStarts.regularStarts N L
  · have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
    have hh := hp N (by omega) L hband H x hx
    rwa [RetainedReferenceTheorem.ground_marginal (by omega) hL x hx] at hh
  · have hzero : PositionalCompoundPoisson.incidence (GoodEdgeCompression.goodEdges H N L)
        (infiniteJointMoment L) x = 0 := by
      unfold PositionalCompoundPoisson.incidence
      apply sum_eq_zero
      intro e he
      have hnot : x ∉ e := fun hxe ↦ hx (RetainedGoodEdges.good_pair_regular (by omega) e he hxe)
      simp only [hnot, ite_false]
    rw [hzero, sub_zero]
    positivity

theorem full_target_isProbability (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      PositivePositionalConvolution.IsProbability
        (PositionalCompoundPoisson.target (dyadicBlock N) (GoodEdgeCompression.goodEdges H N L)
          (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)) := by
  obtain ⟨N₀, hN₀, h⟩ := full_single_rates_positive C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband H
  exact PositionalCompoundPoisson.target_isProbability _ _ _ _
    (fun x _hx ↦ (h N hN L hband H x).le) (fun e _ ↦ infiniteJointMoment_nonneg L e)

end PaperP1.WeakPairIncidence
