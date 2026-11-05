module

public import PaperP1.Asymptotics.TripleActivityClosure
public import PaperP1.Asymptotics.FullFixedActivity
public import PaperP1.Asymptotics.AllPairDeficit
public import PaperP1.Asymptotics.PairActivity
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Model.AllPairDeficitMonotonicity

/-! # The actual-law reconstruction with third activity left symbolic -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleActivityLawReconstruction

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables

theorem uniform_estimates (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        CompatibleActivitySplit.absolute L (G.powersetCard 3) ≤ (N : ℝ) ^ (-1 + min (ε / 16) (1 / 48)) ∧
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)) ≤
          (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L (G.powersetCard 3) + (N : ℝ) ^ (-4 / 3 + ε) := by
  classical
  let δ := min (ε / 16) (1 / 48)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε / 16 := min_le_left _ _
  have hδcap : δ ≤ 1 / 48 := min_le_right _ _
  obtain ⟨NC, _hNC, hc⟩ := TripleActivityClosure.uniform_bounds C δ hδ
  obtain ⟨NT, _hNT, hcoarse⟩ := FullFixedActivity.uniform_range 3 C δ hδ
  obtain ⟨ND, _hND, hd⟩ := AllPairDeficit.article_15_9 2 C δ (by norm_num) hδ
  obtain ⟨NA, _hNA, ha⟩ := PairActivity.uniform_pair_activity C δ hδ
  obtain ⟨NK, _hNK, hk⟩ := PairActivity.uniform_conversion C δ hδ
  obtain ⟨NL, _hNL, hl⟩ := SecondOrderBoundaryCutoff.uniform_large_bound C
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NX, hx⟩ := HalfCountSchedule.factor_absorption 6 (-5 / 8) (1 / 8) (by norm_num)
  let M : ℝ := 2 * (2 : ℝ) ^ C
  let E := Real.exp (2 * M)
  let B := 1 + 18 * Real.exp 1
  let A := 2 * E + 16 + E * B + (2 : ℝ) ^ (2 * C) + 1
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption A 0 (ε / 2) (by positivity)
  refine ⟨10 + NL + NM + NG + NX + NF + NC + NT + ND + NA + NK, by omega, ?_⟩
  intro N hN L hband G hG
  let K := SecondOrderBoundaryCutoff.cutoff C N
  let a := ∑ e ∈ G.powersetCard 2, ActualComponentRemainder.weight L 2 e
  let b := ∑ I ∈ ActualComponentRemainder.higher G L K 2, ActualComponentRemainder.weight L 2 I
  let q := ∑ I ∈ SecondOrderIndependentDeficit.primitives G L, ActualComponentRemainder.weight L 2 I
  let x := a + b
  let V := (N : ℝ) ^ (-2 / 3 + 2 * δ)
  let A3 := CompatibleActivitySplit.absolute L (G.powersetCard 3)
  let P := (N : ℝ) ^ (-4 / 3 + 4 * δ)
  let D := (N : ℝ) ^ δ * A3 + P
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hV : 0 ≤ V := Real.rpow_nonneg hnpos.le _
  have hA3 : 0 ≤ A3 := sum_nonneg fun I _ ↦ abs_nonneg _
  have hP : 0 ≤ P := Real.rpow_nonneg hnpos.le _
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hPD : P ≤ D := le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hnpos.le _) hA3)
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hw (I : Finset ℕ) : 0 ≤ ActualComponentRemainder.weight L 2 I := by
    exact mul_nonneg (by positivity) (abs_nonneg _)
  have ha0 : 0 ≤ a := sum_nonneg fun I _ ↦ hw I
  have hb0 : 0 ≤ b := sum_nonneg fun I _ ↦ hw I
  have hq0 : 0 ≤ q := sum_nonneg fun I _ ↦ hw I
  have hx0 : 0 ≤ x := add_nonneg ha0 hb0
  obtain ⟨hb, hq⟩ := hc N (by omega) L hband G hG
  change b ≤ (N : ℝ) ^ δ * A3 + (N : ℝ) ^ (-4 / 3 + δ) at hb
  change q ≤ (N : ℝ) ^ δ * A3 + (N : ℝ) ^ (-4 / 3 + δ) at hq
  have hcoarseA : A3 ≤ (N : ℝ) ^ (-1 + δ) := by
    have h := hcoarse N (by omega) L hband 3 (by norm_num) le_rfl G hG
    change (∑ I ∈ G.powersetCard 3, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + δ)
    exact h
  have hbD : b ≤ D := hb.trans (add_le_add le_rfl
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ]) :
      (N : ℝ) ^ (-4 / 3 + δ) ≤ P))
  have hqD : q ≤ D := hq.trans (add_le_add le_rfl
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ]) :
      (N : ℝ) ^ (-4 / 3 + δ) ≤ P))
  have hbV : b ≤ 2 * V := by
    have hfirst : (N : ℝ) ^ δ * A3 ≤ V := by
      calc
        _ ≤ (N : ℝ) ^ δ * (N : ℝ) ^ (-1 + δ) := mul_le_mul_of_nonneg_left hcoarseA (by positivity)
        _ = (N : ℝ) ^ (-1 + 2 * δ) := by rw [← Real.rpow_add hnpos]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hsecond : (N : ℝ) ^ (-4 / 3 + δ) ≤ V :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ])
    linarith only [hb, hfirst, hsecond]
  have haV : a ≤ 4 * V := by
    have heq : a = 4 * ∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e| := by
      rw [mul_sum]
      apply sum_congr rfl
      intro e he
      dsimp only [ActualComponentRemainder.weight]
      rw [(mem_powersetCard.mp he).2]
      norm_num
    rw [heq]
    have hweak : (N : ℝ) ^ (-2 / 3 + δ) ≤ V :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ])
    exact mul_le_mul_of_nonneg_left ((ha N (by omega) L hband G hG).trans hweak) (by norm_num)
  have hxV : x ≤ 6 * V := by change a + b ≤ _; linarith only [haV, hbV]
  have hx1 : x ≤ 1 := by
    have hsmall : V ≤ (N : ℝ) ^ (-5 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδcap])
    have hfactor := hx N (by omega)
    have hpow : (N : ℝ) ^ ((-5 / 8 : ℝ) + 1 / 8) ≤ 1 :=
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-5 / 8 : ℝ) + 1 / 8 ≤ 0)).trans_eq (Real.rpow_zero N)
    exact hxV.trans ((mul_le_mul_of_nonneg_left hsmall (by norm_num)).trans (hfactor.trans hpow))
  have hsquare : x ^ 2 ≤ 36 * D := by
    have h := pow_le_pow_left₀ hx0 hxV 2
    have hVpow : V ^ 2 = (N : ℝ) ^ (-4 / 3 + 4 * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      congr 1
      ring
    rw [mul_pow, hVpow, show (6 : ℝ) ^ 2 = 36 by norm_num] at h
    exact h.trans (mul_le_mul_of_nonneg_left hPD (by norm_num))
  have hTaylor := FinitePolymerRemainder.exponential_error a b ha0 hb0
  have hquadratic : (x ^ 2 / 2) * Real.exp x ≤ (18 * Real.exp 1) * D := by
    have h := mul_le_mul (div_le_div_of_nonneg_right hsquare (by norm_num)) (Real.exp_le_exp.mpr hx1)
      (Real.exp_nonneg x) (by positivity : 0 ≤ (36 * D) / 2)
    exact h.trans_eq (by ring)
  have herror : Real.exp x - 1 - a ≤ B * D := by
    change Real.exp x - 1 - a ≤ b + (x ^ 2 / 2) * Real.exp x at hTaylor
    dsimp only [B]
    linarith only [hTaylor, hbD, hquadratic]
  have hmean : (∑ y ∈ G, 2 * infiniteMarginal y L) ≤ 2 * M := by
    rw [← mul_sum]
    have hsum : (∑ y ∈ G, infiniteMarginal y L) ≤ M :=
      (sum_le_sum_of_subset_of_nonneg hG (fun y _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg y L)).trans
        (by simpa only [countMoment_one Subset.rfl] using (hm N (by omega) L hband).2)
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hfree : Real.exp (∑ y ∈ G, 2 * infiniteMarginal y L) ≤ E := Real.exp_le_exp.mpr hmean
  have hprimitive := mul_le_mul hfree hqD hq0 hE
  have hnonlinear := (mul_le_mul_of_nonneg_left herror (Real.exp_nonneg (∑ y ∈ G, 2 * infiniteMarginal y L))).trans
    (mul_le_mul_of_nonneg_right hfree (mul_nonneg hB hD))
  have hdeficit : AllPairExtensionDeficit.deficit G L 2 ≤ D :=
    ((AllPairDeficitMonotonicity.deficit_mono G (dyadicBlock N) hG L 2 (by norm_num)).trans
      (hd N (by omega) L hband)).trans
      ((Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ]) :
        (N : ℝ) ^ (-3 / 2 + δ) ≤ P).trans hPD)
  have hlarge : SecondOrderStoppedLaw.largeMass G L K ≤ (2 : ℝ) ^ (2 * C) * D :=
    (hl N (by omega) L hband G hG).trans (mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ]) :
        (N : ℝ) ^ (-4 : ℝ) ≤ P).trans hPD) (by positivity))
  have hconv := hk N (by omega) L hband G hG
  simp only [_root_.sub_apply] at hconv
  change SignedAtomicDistance.distance (FiniteLawEmbedding.embed (SecondOrderRetainedReference.pairReference G L))
    (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)) ≤
      (N : ℝ) ^ (-5 / 3 + δ) at hconv
  have hconvD : SignedAtomicDistance.distance (FiniteLawEmbedding.embed (SecondOrderRetainedReference.pairReference G L))
      (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)) ≤ D :=
    hconv.trans ((Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ]) :
      (N : ℝ) ^ (-5 / 3 + δ) ≤ P).trans hPD)
  have hfinite := SecondOrderStoppedLaw.finite_bound (by omega : 0 < N) G hG hL K
  change SignedAtomicDistance.distance _ _ ≤ 2 * Real.exp (∑ y ∈ G, 2 * infiniteMarginal y L) * q +
    16 * AllPairExtensionDeficit.deficit G L 2 +
    Real.exp (∑ y ∈ G, 2 * infiniteMarginal y L) * (Real.exp x - 1 - a) + SecondOrderStoppedLaw.largeMass G L K at hfinite
  have htriangle := SignedAtomicDistance.triangle (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
    (FiniteLawEmbedding.embed (SecondOrderRetainedReference.pairReference G L))
    (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L))
  have hbudget : SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
      (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)) ≤ A * D := by
    dsimp only [A]
    linarith only [hfinite, htriangle, hprimitive, hnonlinear, hdeficit, hlarge, hconvD]
  have hconstant : A ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using hf N (by omega)
  refine ⟨hcoarseA, ?_⟩
  calc
    _ ≤ A * D := hbudget
    _ ≤ (N : ℝ) ^ (ε / 2) * D := mul_le_mul_of_nonneg_right hconstant hD
    _ = (N : ℝ) ^ (ε / 2 + δ) * A3 + (N : ℝ) ^ (-4 / 3 + 4 * δ + ε / 2) := by
      dsimp only [D, P]
      rw [mul_add, ← mul_assoc, ← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
      congr 1
      congr 1
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδε, hε])) hA3)
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδε, hε]))

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)) ≤
          (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L (G.powersetCard 3) + (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_estimates C ε hε
  exact ⟨N₀, hN₀, fun N hN L hband G hG ↦ (h N hN L hband G hG).2⟩

theorem article_15_14_symbolic (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference (countMoment (dyadicBlock N) L 1)
            (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L)) ≤
          (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 3) +
          (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_bound C ε hε
  exact ⟨N₀, hN₀, fun N hN L hband ↦ h N hN L hband (dyadicBlock N) Subset.rfl⟩

end PaperP1.TripleActivityLawReconstruction
