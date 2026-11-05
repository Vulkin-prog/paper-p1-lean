module

public import PaperP1.Asymptotics.TwoGoodEdgeSecondMoment
public import PaperP1.Asymptotics.SecondFactorialCorrectionLower
public import PaperP1.Model.GoodEdgePopulationBounds

/-! # The missing O(a_N²) numerical deletion and isolation bounds of T19.10

The actual good-edge family is contained in the raw zero-cutoff channels.
Thus one bound works for every real private-prime cutoff, including empty
families. The normalization is the literal nominal second factorial
correction a_N, with its proved positive lower scale.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpOnceAllCoupling

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.TwoGoodPairMass
  PaperP1.HomogeneousRunMass PaperP1.OnceAllOriginalCoupling

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem actual_second_le_homogeneous (L : ℕ) (hL : 0 < L) (E F : Finset (Finset ℕ)) (hEF : E ⊆ F) :
    (∑ p ∈ ActiveFamilySecondMoment.ordered E, infiniteJointMoment L (p.1 ∪ p.2)) ≤
      HomogeneousEdgeInteractions.second L F := by
  let P := ActiveFamilySecondMoment.ordered E
  have hpoint (p : Finset ℕ × Finset ℕ) (_hp : p ∈ P) :
      infiniteJointMoment L (p.1 ∪ p.2) ≤ if SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2) then
        probability L (p.1 ∪ p.2) else 0 := by
    by_cases hsep : SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2)
    · rw [ite_eq_left hsep]
      exact actual_joint_le L hL _
    · rw [ite_eq_right hsep]
      apply le_of_not_gt
      intro hq
      exact hsep (GoodEdgePositivePalm.separated_of_positive_joint L hL _ hq)
  have hsub : P.filter (fun p ↦ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2)) ⊆
      (F ×ˢ F).filter (fun p ↦ p.1 ≠ p.2 ∧ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2)) := by
    intro p hp
    obtain ⟨hpP, hsep⟩ := mem_filter.mp hp
    obtain ⟨hbox, hne⟩ := mem_filter.mp hpP
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hEF (mem_product.mp hbox).1, hEF (mem_product.mp hbox).2⟩, hne, hsep⟩
  calc
    _ ≤ ∑ p ∈ P, if SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2) then probability L (p.1 ∪ p.2) else 0 :=
      sum_le_sum hpoint
    _ = ∑ p ∈ P.filter (fun p ↦ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2)), probability L (p.1 ∪ p.2) :=
      (sum_filter _ _).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ (probability_pos L (p.1 ∪ p.2)).le)

theorem uniform_second (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
        second H N L ≤ K * SecondFactorialCorrection.value N L ^ 2 := by
  obtain ⟨NU, _hNU, hU⟩ := uniform_homogeneous_second C (1 / 60) (by norm_num)
  obtain ⟨A, hA, NA, _hNA, ha⟩ := HomogeneousChannelMass.uniform_principal_upper C
  obtain ⟨c, hc, NC, _hNC, hlow⟩ := SecondFactorialCorrectionLower.uniform_lower C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨(A ^ 2 + 1) / c ^ 2, by positivity, max 10 (max NU (max NA (max NC NG))), by omega, ?_⟩
  intro N hN L hcrit H
  have hL : 1 ≤ L := by have hh := (hg N (by omega) L hcrit).2.2.1; omega
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let B : ℝ := L * (N : ℝ) ^ (-2 / 3 : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have herr : (N : ℝ) ^ (-41 / 30 + 1 / 60 : ℝ) ≤ B ^ 2 := by
    have heq : (N : ℝ) ^ (-4 / 3 : ℝ) = ((N : ℝ) ^ (-2 / 3 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
      congr 1
      norm_num
    calc
      _ ≤ (N : ℝ) ^ (-4 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ ≤ B ^ 2 := by
        rw [heq]
        apply pow_le_pow_left₀ (by positivity)
        have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hLR (Real.rpow_nonneg hn.le (-2 / 3))
  have hmass := ha N (by omega) L 0 hcrit
  have hmassnon : 0 ≤ PrimitiveNominalMass.mass (HomogeneousChannelMass.rawPrincipal N 0 L) L :=
    sum_nonneg (fun e _ ↦ PrimitiveNominalMass.weight_nonneg L e)
  have hmasssq := pow_le_pow_left₀ hmassnon hmass 2
  have hsecond := (actual_second_le_homogeneous L (by omega) (GoodEdgeCompression.goodEdges H N L)
    (HomogeneousChannelMass.rawPrincipal N 0 L) (RetainedIndependentDeficitComparison.good_subset_zero_channels (by omega) H)).trans
    (hU N (by omega) L 0 hcrit)
  rw [← second_eq_joint (by omega) H] at hsecond
  have hraw : second H N L ≤ (A ^ 2 + 1) * B ^ 2 := by
    dsimp only [B] at herr ⊢
    nlinarith only [hsecond, hmasssq, herr]
  have hlow' := hlow N (by omega) L hcrit
  have hlowB : c * B ≤ SecondFactorialCorrection.value N L := by simpa only [B, mul_assoc] using hlow'
  have hsquare := pow_le_pow_left₀ (mul_nonneg hc.le hB) hlowB 2
  have hsq : B ^ 2 ≤ SecondFactorialCorrection.value N L ^ 2 / c ^ 2 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < c ^ 2)).mpr
    nlinarith only [hsquare]
  calc
    _ ≤ (A ^ 2 + 1) * (SecondFactorialCorrection.value N L ^ 2 / c ^ 2) :=
      hraw.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
    _ = _ := by ring

theorem companion_T19_10_sharp (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
        second H N L ≤ K * SecondFactorialCorrection.value N L ^ 2 ∧
        0 ≤ correction H N L ∧ correction H N L ≤ second H N L / 2 ∧
        totalVariation H N L ≤ second H N L / 2 ∧ wasserstein H N L ≤ second H N L := by
  obtain ⟨K, hK, N₀, hN₀, hU⟩ := uniform_second C
  refine ⟨K, hK, N₀, hN₀, ?_⟩
  intro N hN L hcrit H
  exact ⟨hU N hN L hcrit H, good_bounds (L := L) (by omega : 2 ≤ N) H⟩

end PaperP1.SharpOnceAllCoupling
