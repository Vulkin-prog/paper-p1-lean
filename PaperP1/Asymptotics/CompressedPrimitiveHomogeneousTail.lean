module

public import PaperP1.Asymptotics.CompressedPrimitiveTailCover
public import PaperP1.Asymptotics.HomogeneousChannelWeights
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # Unconditional all-cardinality homogeneous primitive tails retain the pair power -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedPrimitiveHomogeneousTail

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ChannelCompressedPrimitiveSets
  PaperP1.DyadicEndpointPairs

theorem uniform_tail (a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (hb : 3 ≤ b) (hb4 : b ≤ 4) (C w ε : ℝ) (hw : 0 < w) (hε : 0 < ε) :
    ∃ s : ℕ, 2 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      mass N a b L s w ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
  classical
  let K := w * ((2 : ℝ) ^ C) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨s, hs, NT, _hNT, ht⟩ := CompressedBlockIndependentTail.uniform_channel a b hab.le (by omega)
    C w (2 - ε / 8) (ε / 8) hw (by linarith only [hε]) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := HomogeneousChannelWeights.uniform_pair C (ε / 8) a b ha hab hcop (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NS, hscale⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NB, hpoly⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (CriticalBandScale.upperScale ^ 2) 2 (ε / 8) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K
    (-2 + 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨s, hs, 10 + NT + NP + NG + NS + NB + NF, by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hgeom := hg N (by omega) L hband
  have hL : 0 < L := by omega
  have hLN : L ≤ N := by omega
  have hwidth : b * (L + 1) < N := by
    have hh := Nat.mul_le_mul_right (L + 1) hb4
    omega
  have hB := (hscale N (by omega) L hband).2
  have hpolyB : ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ (ε / 8) := by
    calc
      _ ≤ (CriticalBandScale.upperScale * Real.log N) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hB 2
      _ = CriticalBandScale.upperScale ^ 2 * (Real.log N) ^ 2 := mul_pow _ _ _
      _ ≤ _ := by simpa only [Real.rpow_ofNat] using hpoly N (by omega)
  let R := (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 8)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpre : w * R * (2 ^ L : ℝ) ^ 2 ≤ K * (N : ℝ) ^ (1 / (b : ℝ) + ε / 8) := by
    calc
      _ ≤ w * R * ((2 : ℝ) ^ C * N) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (CriticalChannelPowers.word_upper (by omega) hband) 2)
        (mul_nonneg hw.le hR)
      _ = _ := by
        rw [mul_pow]
        conv_rhs => rw [show 1 / (b : ℝ) + ε / 8 = (-2 + 1 / (b : ℝ) + ε / 8) + 2 by ring,
          Real.rpow_add hn, Real.rpow_two]
        dsimp [K, R]
        ring
  have hrow (ij : Fin (L + 1) × Fin (L + 1)) :
      fixedMass N a b L s w ij.1 ij.2 ≤
        (K * (N : ℝ) ^ (1 / (b : ℝ) + ε / 8)) * (N : ℝ) ^ (-2 + ε / 4) := by
    have hfinite := CompressedPrimitiveTailCover.fixed_mass_bound (s := s) (by omega) hL ha (by omega)
      hLN hwidth w R hw hR ij.1 ij.2 (fun xy hxy ↦ hp N (by omega) L hband xy (by
        obtain ⟨hx, hy, hu⟩ := mem_sourcePairs.mp hxy
        exact mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩,
          ⟨(ij.1, ij.2), PaperP1.NormalizedUnitCount.mem_units.mpr hu⟩⟩))
    have htail : BoundedBlockIndependentTail.mass (3 * b + 2) N L s w
        (CompressedBlockIndependentTail.shiftedBlock N a b L ij.1 ij.2) ≤ (N : ℝ) ^ (-2 + ε / 4) := by
      convert ht N (by omega) L hband ij.1 ij.2 using 1
      congr 1
      ring
    exact hfinite.trans ((mul_le_mul_of_nonneg_left htail (mul_nonneg (mul_nonneg hw.le hR) (sq_nonneg _))).trans
      (mul_le_mul_of_nonneg_right hpre (by positivity)))
  calc
    _ ≤ ∑ ij : Fin (L + 1) × Fin (L + 1), fixedMass N a b L s w ij.1 ij.2 :=
      mass_le_offsets N a b L s w hw.le
    _ ≤ ∑ _ij : Fin (L + 1) × Fin (L + 1),
        (K * (N : ℝ) ^ (1 / (b : ℝ) + ε / 8)) * (N : ℝ) ^ (-2 + ε / 4) := sum_le_sum fun ij _ ↦ hrow ij
    _ = ((L + 1 : ℕ) : ℝ) ^ 2 *
        ((K * (N : ℝ) ^ (1 / (b : ℝ) + ε / 8)) * (N : ℝ) ^ (-2 + ε / 4)) := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring
    _ ≤ (N : ℝ) ^ (ε / 8) *
        ((K * (N : ℝ) ^ (1 / (b : ℝ) + ε / 8)) * (N : ℝ) ^ (-2 + ε / 4)) :=
      mul_le_mul_of_nonneg_right hpolyB (mul_nonneg (mul_nonneg hK (by positivity)) (by positivity))
    _ = K * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := by
      calc
        _ = K * ((N : ℝ) ^ (ε / 8) * (N : ℝ) ^ (1 / (b : ℝ) + ε / 8) * (N : ℝ) ^ (-2 + ε / 4)) := by ring
        _ = _ := by rw [← Real.rpow_add hn, ← Real.rpow_add hn]; congr 2; ring
    _ ≤ (N : ℝ) ^ ((-2 + 1 / (b : ℝ) + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.CompressedPrimitiveHomogeneousTail
