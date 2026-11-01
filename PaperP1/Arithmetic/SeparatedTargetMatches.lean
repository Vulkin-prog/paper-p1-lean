module

public import PaperP1.Arithmetic.PhysicalNormalizedMatches

/-! # Actual target matching counts need deterministic separation only -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeparatedTargetMatches

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets
  PaperP1.ActualNormalizedMatches PaperP1.FixedChannelGamma PaperP1.PhysicalNormalizedMatches

theorem match_bound {a b c d x y z L t : ℕ} (ha : 0 < a) (hb : 3 ≤ b)
    (hab : a.Coprime b) (horder : a < b) (hc : 0 < c) (hd : 0 < d) (hcop : c.Coprime d)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsepX : x + L ≤ z ∨ z + L ≤ x) (hsepY : y + L ≤ z ∨ z + L ≤ y)
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
        exact CompatibleWindowOverlap.interval_overlap_le_one hx hz hsepX
      have hbound := physical_a_bound ha (by omega : 0 < b) hab hy hz hoverlap
      linarith
    · subst c
      have hoverlap : (NormalizedWindowSets.values z L ∩ NormalizedWindowSets.values y L).card ≤ 1 := by
        rw [inter_comm]
        exact CompatibleWindowOverlap.interval_overlap_le_one hy hz hsepY
      have hbound := physical_b_bound ha (by omega : 0 < b) hab hx hz hoverlap
      linarith
  · have hca : ¬c ∣ a := fun hca ↦ hdiv (Or.inl hca)
    have hcb : ¬c ∣ b := fun hcb ↦ hdiv (Or.inr hcb)
    have hQ := nonphysical_match_bound ha hb hab hc hd hcop hx hy hz i₀ j₀ h hbaseX hbaseY htarget hlo hhi hca hcb
    have hR := (Rat.cast_le (K := ℝ)).mpr hQ
    norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] at hR
    exact hR

end PaperP1.SeparatedTargetMatches
