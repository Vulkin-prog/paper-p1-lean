module

public import PaperP1.Probability.PositionalMarkedPairExpansion
public import PaperP1.Asymptotics.PositionalInsertedPairRate
public import PaperP1.Asymptotics.RetainedGoodPairMass

/-! # Deleting marked good pairs recovers the independent background at rate one

This full-reference comparison is unconditional; transfer to the original
field uses the already explicit arithmetic inputs of main 20.1.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalCompoundDeletionRate

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw
  PaperP1.FiniteConvolutionAlgebra PaperP1.CompletedPositionalLaw
  PaperP1.PositionalPairDeletion PaperP1.PositionalDeletionKernels

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      let E := GoodEdgeCompression.goodEdges H N L
      let T := PositionalCompoundPoisson.target (dyadicBlock N) E
        (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
      let U := PositionalMarkedPairExpansion.background (dyadicBlock N) E
        (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
      ‖once E T - U‖ ≤ (N : ℝ) ^ (-1 + ε) ∧
      ‖isolated E T - U‖ ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NB, _hNB, hb⟩ := PositionalPoissonAccidentRate.uniform_background_deletion C (ε / 4) (by positivity)
  obtain ⟨NS, _hNS, hs⟩ := PositionalInsertedPairRate.uniform_background C (ε / 4) (by positivity)
  obtain ⟨NQ, _hNQ, hq⟩ := RetainedGoodPairMass.uniform_bound C (1 / 24) (by norm_num)
  obtain ⟨NP, _hNP, hp⟩ := WeakPairIncidence.full_single_rates_positive C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption
    (4 * Real.exp 2 + 2) (-1 + ε / 4) (3 * ε / 4) (by positivity)
  refine ⟨3 + NB + NS + NQ + NP + NF, by omega, ?_⟩
  intro N hN L hband H
  dsimp only
  let G := dyadicBlock N
  let E := GoodEdgeCompression.goodEdges H N L
  let p := fun _x : ℕ ↦ (2 ^ L : ℝ)⁻¹
  let q := infiniteJointMoment L
  let T := PositionalCompoundPoisson.target G E p q
  let U := PositionalMarkedPairExpansion.background G E p q
  let β := ∑ e ∈ E, q e
  let P := (N : ℝ) ^ (-1 + ε / 4)
  let R := (N : ℝ) ^ (-1 / 2 + ε / 4)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hP0 : 0 ≤ P := Real.rpow_nonneg hn.le _
  have hq0 (e : Finset ℕ) (_he : e ∈ E) : 0 ≤ q e := infiniteJointMoment_nonneg L e
  have hβ0 : 0 ≤ β := sum_nonneg hq0
  have hβ : β ≤ (N : ℝ) ^ (-5 / 8 : ℝ) := by
    have hh := hq N (by omega) L hband H
    change β ≤ (N : ℝ) ^ (-2 / 3 + 1 / 24 : ℝ) at hh
    simpa only [show (-2 / 3 + 1 / 24 : ℝ) = -5 / 8 by norm_num] using hh
  have hβ1 : β ≤ 1 := hβ.trans (by
    have hh := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-5 / 8 : ℝ) ≤ 0)
    simpa only [Real.rpow_zero] using hh)
  have hβsq : β ^ 2 ≤ P := by
    have hh := pow_le_pow_left₀ hβ0 hβ 2
    have he : ((N : ℝ) ^ (-5 / 8 : ℝ)) ^ 2 = (N : ℝ) ^ (-5 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
      congr 1
      norm_num
    rw [he] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε] :
      (-5 / 4 : ℝ) ≤ -1 + ε / 4))
  have hβR : β * R ≤ P := by
    calc
      _ ≤ (N : ℝ) ^ (-5 / 8 : ℝ) * R := mul_le_mul_of_nonneg_right hβ (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ) ^ (-5 / 8 + (-1 / 2 + ε / 4)) := by rw [← Real.rpow_add hn]
      _ ≤ P := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [] :
        (-5 / 8 : ℝ) + (-1 / 2 + ε / 4) ≤ -1 + ε / 4)
  have hrem : 4 * β ^ 2 * Real.exp (2 * β) ≤ (4 * Real.exp 2) * P := by
    have hexp : Real.exp (2 * β) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith only [hβ1])
    have hscaled := mul_le_mul_of_nonneg_left hβsq (by norm_num : (0 : ℝ) ≤ 4)
    have hh := mul_le_mul hscaled hexp (Real.exp_nonneg _) (by positivity : 0 ≤ 4 * P)
    nlinarith only [hh]
  have hfactor : (4 * Real.exp 2 + 2) * P ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hsite (x : ℕ) (_hx : x ∈ G) : 0 ≤ p x - PositionalCompoundPoisson.incidence E q x :=
    (hp N (by omega) L hband H x).le
  have hForK (K : Space ℕ →L[ℝ] Space ℕ) (hK : ∀ ν, ‖K ν‖ ≤ ‖ν‖)
      (hBG : ‖K U - U‖ ≤ P)
      (hShift : ∀ e ∈ E, ‖K (ofFinite (atom (edgeVector e)) * U) - U‖ ≤ R) :
      ‖K T - U‖ ≤ (N : ℝ) ^ (-1 + ε) := by
    have hfinite := PositionalMarkedPairExpansion.approximation_bound G E p q hsite hq0 K hK
    change ‖K T - U‖ ≤ 4 * β ^ 2 * Real.exp (2 * β) +
      |1 - β| * ‖K U - U‖ + ∑ e ∈ E, q e * ‖K (ofFinite (atom (edgeVector e)) * U) - U‖ at hfinite
    have habs : |1 - β| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hβ1)]; linarith only [hβ0]
    have hbg : |1 - β| * ‖K U - U‖ ≤ P := by
      have hh := mul_le_mul habs hBG (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [one_mul] using hh
    have hsum : (∑ e ∈ E, q e * ‖K (ofFinite (atom (edgeVector e)) * U) - U‖) ≤ P := by
      calc
        _ ≤ ∑ e ∈ E, q e * R := sum_le_sum (fun e he ↦
          mul_le_mul_of_nonneg_left (hShift e he) (hq0 e he))
        _ = β * R := (sum_mul _ _ _).symm
        _ ≤ P := hβR
    linarith only [hfinite, hrem, hbg, hsum, hfactor]
  have hbackground := hb N (by omega) L hband H
  have hsingle := hs N (by omega) L hband H
  constructor
  · apply hForK (once E) ?_ hbackground.1 (fun e he ↦ (hsingle e he).1)
    intro ν
    have hh := once_contraction E ν 0
    simpa only [map_zero, sub_zero] using hh
  · apply hForK (isolated E) ?_ hbackground.2 (fun e he ↦ (hsingle e he).2)
    intro ν
    have hh := isolated_contraction E ν 0
    simpa only [map_zero, sub_zero] using hh

end PaperP1.PositionalCompoundDeletionRate
