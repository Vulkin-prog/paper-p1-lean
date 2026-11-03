module

public import PaperP1.Asymptotics.FiniteConnectedClosureUnderInputs
public import PaperP1.Asymptotics.AllPairDeficitUnderInputs
public import PaperP1.Asymptotics.FinitePairActivityInputs
public import PaperP1.Asymptotics.SharpRunConversionUnderInputs
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Model.AllPairDeficitMonotonicity

/-! # Article 15.13: exact finite-order transfer to the original complete law, with all heterogeneous and incompatible terms retained -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteCompleteLawTransferUnderInputs

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables

structure Parameters where
  connected : FiniteConnectedClosureUnderInputs.Parameters
  deficitOrder : ℕ
  deficitInitial : FinitePairDeficitInputs.Parameters
  deficitEntries : Fin deficitOrder → FinitePairDeficitInputs.Parameters
  pair : FinitePairDeficitInputs.Parameters
  conversion : FinitePairDeficitInputs.Parameters

structure Hypotheses (p : Parameters) (δ : ℝ) : Prop where
  connected : FiniteConnectedClosureUnderInputs.Hypotheses p.connected δ
  deficitInitial : FinitePairDeficitInputs.Hypotheses p.deficitInitial (GeneralGraphHostCount.sizeCap (δ / 2048))
  deficitEntries : ∀ i, FinitePairDeficitInputs.Hypotheses (p.deficitEntries i) (GeneralGraphHostCount.sizeCap (δ / 65536))
  pair : FinitePairDeficitInputs.Hypotheses p.pair (GeneralGraphHostCount.sizeCap (1 / 100))
  conversion : FinitePairDeficitInputs.Hypotheses p.conversion (GeneralGraphHostCount.sizeCap (1 / 100))

theorem uniform_bound (C β ε : ℝ) (hβ : 1 < β) (hβcap : β ≤ 4 / 3) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (min (ε / 8) (1 / 24)) → FiniteConnectedActivity254.Hypothesis C β →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)) ≤
            (N : ℝ) ^ (-β + ε) := by
  classical
  let δ := min (ε / 8) (1 / 24)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε / 8 := min_le_left _ _
  have hδcap : δ ≤ 1 / 24 := min_le_right _ _
  obtain ⟨pc, hc⟩ := FiniteConnectedClosureUnderInputs.uniform_bounds C β δ hβcap hδ
  obtain ⟨_Q, s, _hQ, _hs, p₀, ps, hd⟩ := AllPairDeficitUnderInputs.article_15_9 2 C δ (by norm_num) hδ
  obtain ⟨pa, ha⟩ := FinitePairActivityInputs.uniform_pair C δ hδ
  obtain ⟨D, k, k₁, k₂, hD, hk⟩ := SharpRunConversionUnderInputs.uniform_conversion C δ hδ
  obtain ⟨NL, _hNL, hl⟩ := SecondOrderBoundaryCutoff.uniform_large_bound C
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NX, hx⟩ := HalfCountSchedule.factor_absorption 5 (-5 / 8) (1 / 8) (by norm_num)
  let M : ℝ := 2 * (2 : ℝ) ^ C
  let E := Real.exp (2 * M)
  let B := 1 + 25 * Real.exp 1 / 2
  let A := 2 * E + 16 + E * B + (2 : ℝ) ^ (2 * C) + 1
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption A (-β + 2 * δ) (ε / 2) (by positivity)
  refine ⟨⟨pc, s, p₀, ps, pa, ⟨D, k, k₁, k₂, hD⟩⟩, ?_⟩
  intro hgeo hfixed
  obtain ⟨NC, _hNC, hc⟩ := hc hgeo.connected hfixed
  have hs₀ : (δ / 16) / 128 = δ / 2048 := by ring
  have hsP : (δ / 16) / 4096 = δ / 65536 := by ring
  obtain ⟨ND, _hND, hd⟩ := hd (by simpa only [hs₀] using hgeo.deficitInitial)
    (by simpa only [hsP] using hgeo.deficitEntries)
  obtain ⟨NA, _hNA, ha⟩ := ha hgeo.pair
  obtain ⟨NK, _hNK, hk⟩ := hk hgeo.conversion.source hgeo.conversion.ordinaryTwo hgeo.conversion.ordinaryThree
    hgeo.conversion.sourceCurves hgeo.conversion.ordinaryTwoCurves hgeo.conversion.ordinaryThreeCurves
  refine ⟨10 + NL + NM + NG + NX + NF + NC + ND + NA + NK, by omega, ?_⟩
  intro N hN L hband G hG
  let K := SecondOrderBoundaryCutoff.cutoff C N
  let a := ∑ e ∈ G.powersetCard 2, ActualComponentRemainder.weight L 2 e
  let b := ∑ I ∈ ActualComponentRemainder.higher G L K 2, ActualComponentRemainder.weight L 2 I
  let q := ∑ I ∈ SecondOrderIndependentDeficit.primitives G L, ActualComponentRemainder.weight L 2 I
  let x := a + b
  let V := (N : ℝ) ^ (-2 / 3 + δ)
  let P := (N : ℝ) ^ (-β + 2 * δ)
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hV : 0 ≤ V := Real.rpow_nonneg hnpos.le _
  have hP : 0 ≤ P := Real.rpow_nonneg hnpos.le _
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hw (I : Finset ℕ) : 0 ≤ ActualComponentRemainder.weight L 2 I := by
    exact mul_nonneg (by positivity) (abs_nonneg _)
  have ha0 : 0 ≤ a := sum_nonneg fun I _ ↦ hw I
  have hb0 : 0 ≤ b := sum_nonneg fun I _ ↦ hw I
  have hq0 : 0 ≤ q := sum_nonneg fun I _ ↦ hw I
  have hx0 : 0 ≤ x := add_nonneg ha0 hb0
  obtain ⟨hb, hq⟩ := hc N (by omega) L hband G hG
  change b ≤ (N : ℝ) ^ (-β + δ) at hb
  change q ≤ (N : ℝ) ^ (-β + δ) at hq
  have hbP : b ≤ P := hb.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ]))
  have hqP : q ≤ P := hq.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ]))
  have hbV : b ≤ V := hb.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hβ]))
  have haV : a ≤ 4 * V := by
    have heq : a = 4 * ∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e| := by
      rw [mul_sum]
      apply sum_congr rfl
      intro e he
      dsimp only [ActualComponentRemainder.weight]
      rw [(mem_powersetCard.mp he).2]
      norm_num
    rw [heq]
    exact mul_le_mul_of_nonneg_left (ha N (by omega) L hband G hG) (by norm_num)
  have hxV : x ≤ 5 * V := by change a + b ≤ _; linarith only [haV, hbV]
  have hx1 : x ≤ 1 := by
    have hsmall : V ≤ (N : ℝ) ^ (-5 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδcap])
    have hfactor := hx N (by omega)
    have hpow : (N : ℝ) ^ ((-5 / 8 : ℝ) + 1 / 8) ≤ 1 :=
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-5 / 8 : ℝ) + 1 / 8 ≤ 0)).trans_eq (Real.rpow_zero N)
    exact hxV.trans ((mul_le_mul_of_nonneg_left hsmall (by norm_num)).trans (hfactor.trans hpow))
  have hsquare : x ^ 2 ≤ 25 * P := by
    have h := pow_le_pow_left₀ hx0 hxV 2
    have hVpow : V ^ 2 = (N : ℝ) ^ (-4 / 3 + 2 * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      congr 1
      ring
    rw [mul_pow, hVpow] at h
    norm_num only [show (5 : ℝ) ^ 2 = 25 by norm_num] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hβcap])) (by norm_num))
  have hTaylor := FinitePolymerRemainder.exponential_error a b ha0 hb0
  have hquadratic : (x ^ 2 / 2) * Real.exp x ≤ (25 * Real.exp 1 / 2) * P := by
    have h := mul_le_mul (div_le_div_of_nonneg_right hsquare (by norm_num)) (Real.exp_le_exp.mpr hx1)
      (Real.exp_nonneg x) (by positivity : 0 ≤ (25 * P) / 2)
    exact h.trans_eq (by ring)
  have herror : Real.exp x - 1 - a ≤ B * P := by
    change Real.exp x - 1 - a ≤ b + (x ^ 2 / 2) * Real.exp x at hTaylor
    dsimp only [B]
    linarith only [hTaylor, hbP, hquadratic]
  have hmean : (∑ y ∈ G, 2 * infiniteMarginal y L) ≤ 2 * M := by
    rw [← mul_sum]
    have hsum : (∑ y ∈ G, infiniteMarginal y L) ≤ M :=
      (sum_le_sum_of_subset_of_nonneg hG (fun y _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg y L)).trans
        (by simpa only [countMoment_one Subset.rfl] using (hm N (by omega) L hband).2)
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hfree : Real.exp (∑ y ∈ G, 2 * infiniteMarginal y L) ≤ E := Real.exp_le_exp.mpr hmean
  have hprimitive := mul_le_mul hfree hqP hq0 hE
  have hnonlinear := (mul_le_mul_of_nonneg_left herror (Real.exp_nonneg (∑ y ∈ G, 2 * infiniteMarginal y L))).trans
    (mul_le_mul_of_nonneg_right hfree (mul_nonneg hB hP))
  have hdeficit : AllPairExtensionDeficit.deficit G L 2 ≤ P :=
    ((AllPairDeficitMonotonicity.deficit_mono G (dyadicBlock N) hG L 2 (by norm_num)).trans
      (hd N (by omega) L hband)).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hβcap, hδ]))
  have hlarge : SecondOrderStoppedLaw.largeMass G L K ≤ (2 : ℝ) ^ (2 * C) * P :=
    (hl N (by omega) L hband G hG).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hβcap, hδ])) (by positivity))
  have hconv := hk N (by omega) L hband G hG
  simp only [_root_.sub_apply] at hconv
  change SignedAtomicDistance.distance (FiniteLawEmbedding.embed (SecondOrderRetainedReference.pairReference G L))
    (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)) ≤
      (N : ℝ) ^ (-5 / 3 + δ) at hconv
  have hconvP : SignedAtomicDistance.distance (FiniteLawEmbedding.embed (SecondOrderRetainedReference.pairReference G L))
      (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)) ≤ P :=
    hconv.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hβcap, hδ]))
  have hfinite := SecondOrderStoppedLaw.finite_bound (by omega : 0 < N) G hG hL K
  change SignedAtomicDistance.distance _ _ ≤ 2 * Real.exp (∑ y ∈ G, 2 * infiniteMarginal y L) * q +
    16 * AllPairExtensionDeficit.deficit G L 2 +
    Real.exp (∑ y ∈ G, 2 * infiniteMarginal y L) * (Real.exp x - 1 - a) + SecondOrderStoppedLaw.largeMass G L K at hfinite
  have htriangle := SignedAtomicDistance.triangle (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
    (FiniteLawEmbedding.embed (SecondOrderRetainedReference.pairReference G L))
    (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L))
  have hbudget : SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
      (QuadraticPoisson.reference (countMoment G L 1) (RegularCumulantTransfer.secondFactorialCumulant G L)) ≤ A * P := by
    dsimp only [A]
    linarith only [hfinite, htriangle, hprimitive, hnonlinear, hdeficit, hlarge, hconvP]
  calc
    _ ≤ A * P := hbudget
    _ ≤ (N : ℝ) ^ ((-β + 2 * δ) + ε / 2) := hf N (by omega)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδε, hε])

theorem article_15_13 (C β ε : ℝ) (hβ : 1 < β) (hβcap : β ≤ 4 / 3) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (min (ε / 8) (1 / 24)) → FiniteConnectedActivity254.Hypothesis C β →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference (countMoment (dyadicBlock N) L 1)
            (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L)) ≤ (N : ℝ) ^ (-β + ε) := by
  obtain ⟨p, hp⟩ := uniform_bound C β ε hβ hβcap hε
  refine ⟨p, ?_⟩
  intro hgeo hfixed
  obtain ⟨N₀, hN₀, h⟩ := hp hgeo hfixed
  exact ⟨N₀, hN₀, fun N hN L hband ↦ h N hN L hband (dyadicBlock N) Subset.rfl⟩

end PaperP1.FiniteCompleteLawTransferUnderInputs
