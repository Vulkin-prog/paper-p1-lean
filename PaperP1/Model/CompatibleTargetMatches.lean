module

public import PaperP1.Arithmetic.PhysicalNormalizedMatches
public import PaperP1.Arithmetic.GoodEdgeCompression

/-! # Actual compatible target matches, including both physical fractions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompatibleTargetMatches

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount PaperP1.ActualNormalizedMatches
  PaperP1.FixedChannelGamma PaperP1.PhysicalNormalizedMatches

theorem goodEdge_parameter {H : ℝ} {N L x y : ℕ} (hN : 2 ≤ N)
    (hgood : GoodEdgeCompression.GoodEdge H N L x y) :
    ∃ a b t : ℕ, GoodEdgeCompression.Leading a b ∧ 0 < t ∧
      ∃ i₀ j₀ : Fin (L + 1), startCompleteVertexLabel x L i₀ = a * t ∧
        startCompleteVertexLabel y L j₀ = b * t := by
  obtain ⟨hx, hy, _, _, hdep, a, b, hlead, hprivate⟩ := hgood
  obtain ⟨ha, hb, hab, _, _⟩ := GoodEdgeCompression.leading_properties hlead
  have hx2 : 2 ≤ x := hN.trans (mem_Ico.mp hx).1
  have hy2 : 2 ≤ y := hN.trans (mem_Ico.mp hy).1
  have htwo := CompressionRank.dependent_two_units ha hb hx2 hy2 hprivate.private hdep
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < (units a b x y L).card by omega)
  obtain ⟨t, ht, hbaseX, hbaseY⟩ := ExactMatchCongruences.source_parameter ha hab hx2 u.1 u.2 (mem_units.mp hu)
  exact ⟨a, b, t, hlead, ht, u.1, u.2, hbaseX, hbaseY⟩

theorem compatible_match_bound {a b c d x y z L t : ℕ} (ha : 0 < a) (hb : 3 ≤ b)
    (hab : a.Coprime b) (horder : a < b) (hc : 0 < c) (hd : 0 < d) (hcop : c.Coprime d)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hL : 0 < L) (hxz : x ≠ z) (hyz : y ≠ z)
    (hqx : 0 < infiniteJointMoment L {x, z}) (hqy : 0 < infiniteJointMoment L {y, z})
    (i₀ j₀ : Fin (L + 1)) (h : ℤ)
    (hbaseX : startCompleteVertexLabel x L i₀ = a * t)
    (hbaseY : startCompleteVertexLabel y L j₀ = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hlo : (b : ℚ) / 2 < (c : ℚ) / d) (hhi : (c : ℚ) / d < 2 * a) :
    ((exactOffsets a b c d x y z L).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) * gammaReal a b + 3 := by
  have hbase : 1 / (b : ℝ) ≤ gammaReal a b := by
    have hR := (Rat.cast_le (K := ℝ)).mpr (base_le_gamma a b)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] at hR
    exact hR
  have hcoef := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg (α := ℝ) (L + 1))
  rw [mul_one_div] at hcoef
  by_cases hdiv : c ∣ a ∨ c ∣ b
  · obtain ⟨hphysical, hd1⟩ := FixedChannelMatches.physical_fraction_of_divisor ha horder hd
      ((ratio_conditions hd).mp ⟨hlo, hhi⟩).1 hdiv
    subst d
    rcases hphysical with hca | hcb
    · subst c
      have hoverlap : (NormalizedWindowSets.values z L ∩ NormalizedWindowSets.values x L).card ≤ 1 := by
        rw [inter_comm]
        exact CompatibleWindowOverlap.compatible_pair_overlap_le_one hx hz hxz hL hqx
      have hbound := physical_a_bound ha (by omega : 0 < b) hab hy hz hoverlap
      linarith
    · subst c
      have hoverlap : (NormalizedWindowSets.values z L ∩ NormalizedWindowSets.values y L).card ≤ 1 := by
        rw [inter_comm]
        exact CompatibleWindowOverlap.compatible_pair_overlap_le_one hy hz hyz hL hqy
      have hbound := physical_b_bound ha (by omega : 0 < b) hab hx hz hoverlap
      linarith
  · have hca : ¬c ∣ a := fun hca ↦ hdiv (Or.inl hca)
    have hcb : ¬c ∣ b := fun hcb ↦ hdiv (Or.inr hcb)
    have hQ := nonphysical_match_bound ha hb hab hc hd hcop hx hy hz i₀ j₀ h hbaseX hbaseY htarget hlo hhi hca hcb
    have hR := (Rat.cast_le (K := ℝ)).mpr hQ
    norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at hR
    exact hR

theorem compatible_triple_match_bound {a b c d x y z L t : ℕ} (ha : 0 < a) (hb : 3 ≤ b)
    (hab : a.Coprime b) (horder : a < b) (hc : 0 < c) (hd : 0 < d) (hcop : c.Coprime d)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hL : 0 < L) (hxz : x ≠ z) (hyz : y ≠ z)
    (hq : 0 < infiniteJointMoment L {x, y, z})
    (i₀ j₀ : Fin (L + 1)) (h : ℤ)
    (hbaseX : startCompleteVertexLabel x L i₀ = a * t)
    (hbaseY : startCompleteVertexLabel y L j₀ = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hlo : (b : ℚ) / 2 < (c : ℚ) / d) (hhi : (c : ℚ) / d < 2 * a) :
    ((exactOffsets a b c d x y z L).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) * gammaReal a b + 3 := by
  obtain ⟨hqx, hqy⟩ := CompatibleWindowOverlap.triple_joint_pairs hq
  exact compatible_match_bound ha hb hab horder hc hd hcop hx hy hz hL hxz hyz hqx hqy
    i₀ j₀ h hbaseX hbaseY htarget hlo hhi

end PaperP1.CompatibleTargetMatches
