module

public import PaperP1.Model.PrivateChannelRemoval
public import PaperP1.Model.DyadicUnitFourierAggregate

/-! # An actual fixed-channel mass bound with explicit endpoint, bad-host and baseline errors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateChannelMassBound

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrivateChannelSources PaperP1.PrivateChannelRemoval PaperP1.NormalizedDefectSources
  PaperP1.PrivateUnitCovariance PaperP1.DyadicUnitFourierAggregate

theorem mass_exact_decomposition {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) (hL : 0 < L) :
    channelMass N H a b L = ((2 ^ L : ℝ)⁻¹) ^ 2 *
      (2 * (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, signedUnitSum a b x y L) +
        2 * (goodSources N H a b L).card -
        2 * (∑ xy ∈ badSources N H a b L, signedUnitSum a b xy.1 xy.2 L)) := by
  have hAll : (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, signedUnitSum a b x y L) =
      (∑ xy ∈ goodSources N H a b L, signedUnitSum a b xy.1 xy.2 L) +
      (∑ xy ∈ badSources N H a b L, signedUnitSum a b xy.1 xy.2 L) :=
    (sum_product _ _ (fun xy : ℕ × ℕ ↦ signedUnitSum a b xy.1 xy.2 L)).symm.trans
      (signed_sum_partition N H a b L)
  rw [channel_mass_twice_forward hN hab hlarge, forward_mass_formula hN ha hab hlarge hL, hAll]
  ring

theorem three_term_bound (E G V : ℝ) (hG : 0 ≤ G) :
    |E + 2 * G - 2 * V| ≤ |E| + 2 * G + 2 * |V| := by
  have h₁ := abs_add_le E (2 * G)
  have h₂ := abs_add_le (E + 2 * G) (-(2 * V))
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * G)] at h₁
  rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h₂
  rw [sub_eq_add_neg]
  linarith

theorem finite_mass_error {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) (hL : 0 < L) :
    |channelMass N H a b L - ((2 ^ L : ℝ)⁻¹) ^ 2 *
      ((N : ℝ) * (ActualSourceTranslations.coefficient a b : ℝ) * (ChannelSumIdentity.signed L a b : ℤ))| ≤
      ((2 ^ L : ℝ)⁻¹) ^ 2 *
        (6 * ((L + 1 : ℕ) : ℝ) * (ChannelSumIdentity.unsigned L a b : ℤ) +
          2 * ((L + 1 : ℕ) : ℝ) ^ 2 * N +
          2 * ((badSources N H a b L).card : ℝ) * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b)) := by
  let P : ℝ := ((2 ^ L : ℝ)⁻¹) ^ 2
  let E : ℝ := 2 * (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, signedUnitSum a b x y L) -
    (N : ℝ) * (ActualSourceTranslations.coefficient a b : ℝ) * (ChannelSumIdentity.signed L a b : ℤ)
  let G : ℝ := (goodSources N H a b L).card
  let V : ℝ := ∑ xy ∈ badSources N H a b L, signedUnitSum a b xy.1 xy.2 L
  have hP : 0 ≤ P := sq_nonneg _
  have hE : |E| ≤ 6 * ((L + 1 : ℕ) : ℝ) * (ChannelSumIdentity.unsigned L a b : ℤ) :=
    finite_signed_sum_error hN ha hab hinterior hcop hlarge
  have hG : G ≤ ((L + 1 : ℕ) : ℝ) ^ 2 * N := by
    dsimp only [G]
    exact_mod_cast good_sources_card (H := H) (b := b) (L := L) (by omega : 0 < N) ha
  have hV : |V| ≤ ((badSources N H a b L).card : ℝ) * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) :=
    bad_signed_sum_bound hN ha (ha.trans hab) hcop
  have heq : channelMass N H a b L - P *
      ((N : ℝ) * (ActualSourceTranslations.coefficient a b : ℝ) * (ChannelSumIdentity.signed L a b : ℤ)) =
        P * (E + 2 * G - 2 * V) := by
    rw [mass_exact_decomposition hN ha hab hlarge hL]
    dsimp only [P, E, G, V]
    ring
  rw [heq, abs_mul, abs_of_nonneg hP]
  apply mul_le_mul_of_nonneg_left _ hP
  have ht := three_term_bound E G V (Nat.cast_nonneg _)
  nlinarith only [ht, hE, hG, hV]

end PaperP1.PrivateChannelMassBound
