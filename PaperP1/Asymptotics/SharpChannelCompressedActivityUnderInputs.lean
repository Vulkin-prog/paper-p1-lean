module

public import PaperP1.Asymptotics.ChannelCompressedActivityBounds
public import PaperP1.Asymptotics.EffectiveCompressedPrimitiveHomogeneousMassUnderInputs
public import PaperP1.Asymptotics.CompressedPairMassUnderInputs

/-! # Companion T15.1 with the stronger separated exponent41/30 in both channels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpChannelCompressedActivityUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ChannelCompressedActivityBounds

structure Parameters where
  dense : DensePrimitiveTripleMassUnderInputs.Parameters
  sourceDegree : ℕ
  sourceRadicals : ℕ
  ordinaryRadicals : ℕ
  ordinarySize : ℕ

structure Hypotheses (p : Parameters) (b : ℕ) (ε : ℝ) : Prop where
  dense : DensePrimitiveTripleMassUnderInputs.Hypotheses p.dense
  source : UniformSourceSurfaceCover.UniformCover p.sourceRadicals
    (AsymmetricComponentHostCount.sizeCap (2 * b + 1) (ε / 512)) p.sourceDegree
  ordinary : UniformOrdinarySurfaceCover.UniformCover p.ordinaryRadicals (p.ordinarySize + 1)
  sourceCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound
    ((p.sourceDegree + 2).choose 2 + p.sourceRadicals) M
  ordinaryCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound (p.ordinaryRadicals + 3) M

theorem uniform_bound (a b : ℕ) (ha : 0 < a) (hab : a < b) (hint : b < 2 * a)
    (hcop : a.Coprime b) (hb : 3 ≤ b) (hb4 : b ≤ 4) (C w ε : ℝ)
    (hw : 0 < w) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p b ε →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CompressedPairMass.mass (separated N H a b L) L w ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨pd, hd⟩ := EffectiveCompressedPrimitiveHomogeneousMassUnderInputs.uniform_mass
    a b ha hab hcop hb hb4 C w (ε / 2) hw (by positivity)
  obtain ⟨Ds, kg, ko, K, _hDs, _hK, hs⟩ := HomogeneousEffectiveGoodPairExtensionsUnderInputs.uniform_mass
    a b ha hab hint hcop C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (4 + 4 * w ^ 3)
    (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨⟨pd, Ds, kg, ko, K⟩, ?_⟩
  intro hp
  obtain ⟨ND, _hND, hd⟩ := hd hp.dense
  obtain ⟨NS, _hNS, hs⟩ := hs
    (by simpa only [div_div, show (2 : ℝ) * 256 = 512 by norm_num] using hp.source)
    hp.ordinary hp.sourceCurves hp.ordinaryCurves
  refine ⟨10 + ND + NS + NG + NF, by omega, ?_⟩
  intro N hN L H hband
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hrecip : 1 / (b : ℝ) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast hb)
  have hhigh := (high_mass_bound (N := N) (H := H) (a := a) (b := b) hL w hw.le).trans
    (mul_le_mul_of_nonneg_left ((hd N (by omega) L hband).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hrecip] :
        -2 + 1 / (b : ℝ) + ε / 2 ≤ -41 / 30 + ε / 2))) (by norm_num : (0 : ℝ) ≤ 4))
  have hsingle := (single_mass_bound (N := N) (H := H) (a := a) (b := b) hL w hw.le).trans
    (mul_le_mul_of_nonneg_left (hs N (by omega) L H hband) (by positivity : (0 : ℝ) ≤ 4 * w ^ 3))
  have hsplit := separated_mass_bound N H a b L w hw.le
  calc
    _ ≤ (4 + 4 * w ^ 3) * (N : ℝ) ^ (-41 / 30 + ε / 2) := by
      nlinarith only [hhigh, hsingle, hsplit]
    _ ≤ (N : ℝ) ^ ((-41 / 30 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem companion_T15_1_separated (C w ε : ℝ) (hw : 0 < w) (hε : 0 < ε) :
    ∃ p23 p34 : Parameters, Hypotheses p23 3 ε → Hypotheses p34 4 ε →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CompressedPairMass.mass (separated N H 2 3 L) L w ≤ (N : ℝ) ^ (-41 / 30 + ε) ∧
      CompressedPairMass.mass (separated N H 3 4 L) L w ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨p23, h23⟩ := uniform_bound 2 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) C w ε hw hε
  obtain ⟨p34, h34⟩ := uniform_bound 3 4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) C w ε hw hε
  refine ⟨p23, p34, ?_⟩
  intro hp23 hp34
  obtain ⟨N23, _hN23, h23⟩ := h23 hp23
  obtain ⟨N34, _hN34, h34⟩ := h34 hp34
  exact ⟨max 10 (max N23 N34), by omega, fun N hN L H hband ↦
    ⟨h23 N (by omega) L H hband, h34 N (by omega) L H hband⟩⟩

theorem companion_T15_1 (C w ε : ℝ) (hw : 0 < w) (hε : 0 < ε) :
    ∃ p23 p34 : Parameters, ∃ pall : CompressedPairMassUnderInputs.Parameters,
      Hypotheses p23 3 ε → Hypotheses p34 4 ε → CompressedPairMassUnderInputs.Hypotheses pall ε →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CompressedPairMass.mass (separated N H 2 3 L) L w ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
      CompressedPairMass.mass (separated N H 3 4 L) L w ≤ (N : ℝ) ^ (-5 / 4 + ε) ∧
      CompressedPairMass.mass (pairs N H 2 3 L) L w ≤ (N : ℝ) ^ (-1 + ε) ∧
      CompressedPairMass.mass (pairs N H 3 4 L) L w ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨p23, p34, hs⟩ := companion_T15_1_separated C w ε hw hε
  obtain ⟨pall, ha⟩ := CompressedPairMassUnderInputs.uniform_subfamily w C ε hw hε
  refine ⟨p23, p34, pall, ?_⟩
  intro hp23 hp34 hpall
  obtain ⟨NS, _hNS, hs⟩ := hs hp23 hp34
  obtain ⟨NA, _hNA, ha⟩ := ha hpall
  refine ⟨max 10 (max NS NA), by omega, ?_⟩
  intro N hN L H hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsharp := hs N (by omega) L H hband
  exact ⟨hsharp.1.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [])),
    hsharp.2.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [])),
    ha N (by omega) L hband _ Subset.rfl _ (filter_subset _ _),
    ha N (by omega) L hband _ Subset.rfl _ (filter_subset _ _)⟩

end PaperP1.SharpChannelCompressedActivityUnderInputs
