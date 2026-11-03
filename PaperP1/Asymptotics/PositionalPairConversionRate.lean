module

public import PaperP1.Probability.PositionalPairConversion
public import PaperP1.Model.PositionalRetainedReference
public import PaperP1.Asymptotics.RetainedGoodPairMass
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Asymptotics.OriginalWindowFamilyMass

/-! # The original good-edge positional pair reference converts at the stronger rate one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalPairConversionRate

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Arithmetic PaperP1.CompletedPositionalLaw
  PaperP1.PositionalPairConversion

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      let G := RegularStarts.regularStarts N L
      let E := GoodEdgeCompression.goodEdges H N L
      ‖reference G E (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L) -
        PositionalCompoundPoisson.target G E (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L)‖ ≤
        (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨K, hK, NP, hp⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NB, _hNB, hb⟩ := RetainedGoodPairMass.uniform_bound C (1 / 12) (by norm_num)
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NK, hNK⟩ := exists_nat_gt K
  let M : ℝ := 2 * (2 : ℝ) ^ C
  let A : ℝ := 20 * K * M * Real.exp (2 * M) + 16 * K + 16 * Real.exp 4
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption A (-1) ε hε
  refine ⟨10 + NP + NB + NM + NK + NA, by omega, ?_⟩
  intro N hN L hband H
  dsimp only
  let G := RegularStarts.regularStarts N L
  let E := GoodEdgeCompression.goodEdges H N L
  let p := fun x ↦ infiniteMarginal x L
  let q := infiniteJointMoment L
  let β := ∑ e ∈ E, q e
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hKN : K ≤ (N : ℝ) := by
    have hh : (NK : ℝ) ≤ N := by exact_mod_cast (show NK ≤ N by omega)
    linarith only [hNK, hh]
  have hcap (x : ℕ) (hx : x ∈ G) : p x ≤ K / N :=
    (hp N (by omega) L x hband (RegularStarts.regularStarts_subset N L hx)).2
  have hprob (x : ℕ) (hx : x ∈ G) : 0 ≤ p x ∧ p x ≤ 1 :=
    ⟨MissingBlockProbabilities.infiniteMarginal_nonneg x L,
      (hcap x hx).trans ((div_le_one hn).mpr hKN)⟩
  have hmean : (∑ x ∈ G, p x) ≤ M := by
    rw [← CountObservables.countMoment_one (RegularStarts.regularStarts_subset N L)]
    exact (CriticalActualMean.mean_mono (RegularStarts.regularStarts_subset N L) Subset.rfl).trans
      (hm N (by omega) L hband).2
  have hV : (∑ x ∈ G, (p x) ^ 2) ≤ (K / N) * M := by
    calc
      _ ≤ ∑ x ∈ G, (K / N) * p x := sum_le_sum fun x hx ↦ by
        simpa only [pow_two] using mul_le_mul_of_nonneg_right (hcap x hx) (hprob x hx).1
      _ = (K / N) * ∑ x ∈ G, p x := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean (div_nonneg hK.le hn.le)
  have hβ0 : 0 ≤ β := sum_nonneg fun e _ ↦ infiniteJointMoment_nonneg L e
  have hβ : β ≤ (N : ℝ) ^ (-7 / 12 : ℝ) := by
    change (∑ e ∈ GoodEdgeCompression.goodEdges H N L, infiniteJointMoment L e) ≤ _
    simpa only [RetainedReferenceTheorem.beta, show (-2 / 3 : ℝ) + 1 / 12 = -7 / 12 by ring] using
      hb N (by omega) L hband H
  have hβ1 : β ≤ 1 := hβ.trans ((Real.rpow_le_rpow_of_exponent_le hn1
    (by norm_num : (-7 / 12 : ℝ) ≤ 0)).trans_eq (Real.rpow_zero N))
  have hβsq : β ^ 2 ≤ (N : ℝ)⁻¹ := by
    have hh := pow_le_pow_left₀ hβ0 hβ 2
    have he : ((N : ℝ) ^ (-7 / 12 : ℝ)) ^ 2 = (N : ℝ) ^ (-7 / 6 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
      congr 1
      norm_num
    rw [he] at hh
    exact hh.trans ((Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-7 / 6 : ℝ) ≤ -1)).trans_eq
      (Real.rpow_neg_one _))
  have hfinite := conversion_bound G E p q (fun e he ↦
    ⟨RetainedGoodEdges.good_pair_regular (by omega) e he, RetainedGoodEdges.good_pair_card H N L e he⟩)
    hprob (fun e _ ↦ infiniteJointMoment_nonneg L e) (K / N) M hcap hmean
  have hF0 : 0 ≤ 4 * (∑ x ∈ G, (p x) ^ 2) * Real.exp (2 * M) := by positivity
  have hF := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV (by norm_num : (0 : ℝ) ≤ 4))
    (Real.exp_nonneg (2 * M))
  have hfirst : (1 + 4 * β) * (4 * (∑ x ∈ G, (p x) ^ 2) * Real.exp (2 * M)) ≤
      20 * K * M * Real.exp (2 * M) / N := by
    have hh := mul_le_mul (show 1 + 4 * β ≤ 5 by linarith only [hβ1]) hF hF0 (by norm_num)
    exact hh.trans_eq (by ring)
  have hsecond : 16 * (K / N) * β ≤ 16 * K / N := by
    have hh := mul_le_mul_of_nonneg_left hβ1 (by positivity : 0 ≤ 16 * (K / N))
    exact hh.trans_eq (by ring)
  have hthird : 16 * β ^ 2 * Real.exp (4 * β) ≤ 16 * Real.exp 4 / N := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hβsq (by norm_num : (0 : ℝ) ≤ 16))
      (Real.exp_le_exp.mpr (by linarith only [hβ1] : 4 * β ≤ 4)) (Real.exp_nonneg _)
      (by positivity : 0 ≤ 16 * (N : ℝ)⁻¹)
    exact hh.trans_eq (by ring)
  have hbudget : ‖reference G E p q - PositionalCompoundPoisson.target G E p q‖ ≤ A / N := by
    change ‖reference G E p q - PositionalCompoundPoisson.target G E p q‖ ≤
      (1 + 4 * β) * (4 * (∑ x ∈ G, (p x) ^ 2) * Real.exp (2 * M)) +
        16 * (K / N) * β + 16 * β ^ 2 * Real.exp (4 * β) at hfinite
    have he : A / N = 20 * K * M * Real.exp (2 * M) / N + 16 * K / N + 16 * Real.exp 4 / N := by
      dsimp only [A]
      ring
    rw [he]
    linarith only [hfinite, hfirst, hsecond, hthird]
  calc
    _ ≤ A / N := hbudget
    _ = A * (N : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; ring
    _ ≤ _ := ha N (by omega)

end PaperP1.PositionalPairConversionRate
