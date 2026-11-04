module

public import PaperP1.Model.IntervalUnitFourierAggregate
public import PaperP1.Asymptotics.MacroscopicChannelTranslations
public import PaperP1.Arithmetic.ChannelUnsignedBound
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Asymptotics.LogarithmicWordPowers

/-! # Actual leading rational-unit sums with both orientations

The unsigned and predecessor-signed sums use every actual pair of roots.
Finite endpoint errors preserve the signed main term and are bounded by
the positive channel sum. No assumed channel mass enters these theorems.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicLeadingUnitSums

open Finset PaperP1.Arithmetic PaperP1.MacroscopicIntervalGeometry
  PaperP1.UnsignedUnitFourierAggregate PaperP1.PrivateUnitCovariance
  PaperP1.ChannelSumIdentity PaperP1.CriticalBandScale

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def unsignedTotal (M : ℕ) (δ : ℝ) (L : ℕ) : ℝ :=
  2 * ∑ x ∈ starts M δ, ∑ y ∈ starts M δ, unitWeight 1 2 x y L

def signedTotal (M : ℕ) (δ : ℝ) (L : ℕ) : ℝ :=
  2 * ∑ x ∈ starts M δ, ∑ y ∈ starts M δ, signedUnitSum 1 2 x y L

theorem uniform_ceil_errors (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      let lo := ⌈(M : ℝ) ^ δ⌉₊
      |unsignedTotal M δ L - ((M : ℝ) - 2 * lo) * (unsigned L 1 2 : ℤ)| ≤
        6 * ((L + 1 : ℕ) : ℝ) * (unsigned L 1 2 : ℤ) ∧
      |signedTotal M δ L - ((M : ℝ) - 2 * lo) * (signed L 1 2 : ℤ)| ≤
        6 * ((L + 1 : ℕ) : ℝ) * (unsigned L 1 2 : ℤ) := by
  obtain ⟨M₀, hG⟩ := PaperP1.MacroscopicChannelTranslations.uniform_geometry C δ hδ hδ1
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit
  obtain ⟨hlo, hloM, hlarge, hwidth⟩ := hG M hM L hcrit
  let lo := ⌈(M : ℝ) ^ δ⌉₊
  have hlarge' : (1 + 2) * (L + 1) + 1 * L < lo := by simpa only [one_mul] using hlarge
  have hwidth' : 2 * lo + (1 + 2) * (L + 1) ≤ 1 * M := by simpa only [one_mul] using hwidth
  have hunsigned := PaperP1.IntervalUnitFourierAggregate.unsigned_error hlo (by omega : 0 < 1)
    (by omega : 1 < 2) (by norm_num : Nat.Coprime 1 2) hloM hlarge' hwidth'
  have hsigned := PaperP1.IntervalUnitFourierAggregate.signed_error hlo (by omega : 0 < 1)
    (by omega : 1 < 2) (by norm_num : Nat.Coprime 1 2) hloM hlarge' hwidth'
  have hU : (0 : ℚ) ≤ (unsigned L 1 2 : ℤ) := by exact_mod_cast PaperP1.ChannelWordHosts.unsigned_nonneg (L := L) (by omega : 0 < 2) (by omega : 1 ≤ 2)
  have hB : (1 : ℚ) ≤ ((L + 1 : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ L + 1 by omega)
  norm_num only [Nat.cast_one, Nat.cast_ofNat, div_one] at hunsigned hsigned
  have hfactor : 2 * ((M : ℚ) / 2 - lo) = (M : ℚ) - 2 * lo := by ring
  rw [hfactor] at hunsigned hsigned
  have hbound : (2 * (((L + 1 : ℕ) : ℚ) + ((L + 1 : ℕ) : ℚ) / 2 + 1)) * (unsigned L 1 2 : ℤ) ≤
      6 * ((L + 1 : ℕ) : ℚ) * (unsigned L 1 2 : ℤ) :=
    mul_le_mul_of_nonneg_right (by linarith only [hB]) hU
  have huR := (Rat.cast_le (K := ℝ)).mpr (hunsigned.trans hbound)
  have hsR := (Rat.cast_le (K := ℝ)).mpr (hsigned.trans hbound)
  norm_num only [Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_ofNat] at huR hsR
  have huEq := PaperP1.IntervalUnitFourierAggregate.unsigned_symmetric_sum (hi := M) hlo (by omega : 0 < 1)
    (by omega : 1 < 2) (by norm_num : Nat.Coprime 1 2) hlarge'
  have hsEq := PaperP1.IntervalUnitFourierAggregate.signed_symmetric_sum (hi := M) hlo (by omega : 0 < 1)
    (by omega : 1 < 2) (by norm_num : Nat.Coprime 1 2) hlarge'
  change unsignedTotal M δ L = (PaperP1.IntervalUnitFourierAggregate.unsignedHosts lo M L 1 2 : ℝ) at huEq
  change signedTotal M δ L = (PaperP1.IntervalUnitFourierAggregate.signedHosts lo M L 1 2 : ℝ) at hsEq
  rw [← huEq] at huR
  rw [← hsEq] at hsR
  exact ⟨huR, hsR⟩

theorem remove_ceiling_error {M L : ℕ} {δ A S U : ℝ} (hU : 0 ≤ U) (hS : |S| ≤ U)
    (herror : |A - ((M : ℝ) - 2 * ⌈(M : ℝ) ^ δ⌉₊) * S| ≤ 6 * ((L + 1 : ℕ) : ℝ) * U) :
    |A - ((M : ℝ) - 2 * (M : ℝ) ^ δ) * S| ≤ 8 * ((L + 1 : ℕ) : ℝ) * U := by
  let lo := ⌈(M : ℝ) ^ δ⌉₊
  have hceil : (lo : ℝ) < (M : ℝ) ^ δ + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg M) δ)
  have hlo : (M : ℝ) ^ δ ≤ lo := Nat.le_ceil _
  have hcoeff : |((M : ℝ) - 2 * lo) - ((M : ℝ) - 2 * (M : ℝ) ^ δ)| ≤ 2 :=
    abs_le.mpr ⟨by linarith only [hceil], by linarith only [hlo]⟩
  have hshift : |((M : ℝ) - 2 * lo) * S - ((M : ℝ) - 2 * (M : ℝ) ^ δ) * S| ≤ 2 * U := by
    rw [← sub_mul, abs_mul]
    exact mul_le_mul hcoeff hS (abs_nonneg _) (by norm_num)
  have hB : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ L + 1 by omega)
  have hBU := mul_le_mul_of_nonneg_right hB hU
  exact (abs_sub_le A (((M : ℝ) - 2 * lo) * S) (((M : ℝ) - 2 * (M : ℝ) ^ δ) * S)).trans
    (by linarith only [herror, hshift, hBU])

theorem uniform_real_errors (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      |unsignedTotal M δ L - ((M : ℝ) - 2 * (M : ℝ) ^ δ) * (unsigned L 1 2 : ℤ)| ≤
        8 * ((L + 1 : ℕ) : ℝ) * (unsigned L 1 2 : ℤ) ∧
      |signedTotal M δ L - ((M : ℝ) - 2 * (M : ℝ) ^ δ) * (signed L 1 2 : ℤ)| ≤
        8 * ((L + 1 : ℕ) : ℝ) * (unsigned L 1 2 : ℤ) := by
  obtain ⟨M₀, h⟩ := uniform_ceil_errors C δ hδ hδ1
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit
  obtain ⟨hu, hs⟩ := h M hM L hcrit
  have hU : (0 : ℝ) ≤ (unsigned L 1 2 : ℤ) := by exact_mod_cast PaperP1.ChannelWordHosts.unsigned_nonneg (L := L) (by omega : 0 < 2) (by omega : 1 ≤ 2)
  have hS : |((signed L 1 2 : ℤ) : ℝ)| ≤ (unsigned L 1 2 : ℤ) := by
    exact_mod_cast PaperP1.ChannelWordHosts.signed_abs_le_unsigned (L := L) (by omega : 0 < 2) (by omega : 1 ≤ 2)
  exact ⟨remove_ceiling_error hU (le_of_eq (abs_of_nonneg hU)) hu, remove_ceiling_error hU hS hs⟩

theorem endpoint_rate (C ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      8 * ((L + 1 : ℕ) : ℝ) * (unsigned L 1 2 : ℤ) ≤ (M : ℝ) ^ (1 / 2 + ε) := by
  let K : ℝ := (2 : ℝ) ^ ((C + 1) / 2)
  obtain ⟨MB, hB⟩ := critical_band_scale C
  obtain ⟨MP, hP⟩ := PaperP1.LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le (8 * K) 3 ε hε
  refine ⟨max MB MP, ?_⟩
  intro M hM L hcrit
  have hm2 : 2 ≤ M := by omega
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hroot : (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / 2) ≤ K * (M : ℝ) ^ (1 / 2 : ℝ) := by
    simpa only [Nat.cast_ofNat] using PaperP1.CriticalChannelPowers.window_root_upper hm2 (by omega : 0 < 2) hcrit
  have hpoly : 8 * K * ((L + 1 : ℕ) : ℝ) ^ 3 ≤ (M : ℝ) ^ ε := by
    have hp := hP M (by omega) L (hB M (by omega) L hcrit).2
    rw [abs_of_nonneg (by dsimp [K]; positivity : (0 : ℝ) ≤ 8 * K * (L + 1 : ℝ) ^ 3)] at hp
    simpa only [Nat.cast_add, Nat.cast_one] using hp
  have hupper := PaperP1.ChannelUnsignedBound.unsigned_upper_rpow (L := L) (by omega : 0 < 2) (by omega : 1 ≤ 2)
  norm_num only [Nat.cast_ofNat] at hupper
  calc
    _ ≤ 8 * ((L + 1 : ℕ) : ℝ) * (((L + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ ≤ 8 * ((L + 1 : ℕ) : ℝ) * (((L + 1 : ℕ) : ℝ) ^ 2 * (K * (M : ℝ) ^ (1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hroot (sq_nonneg _)) (by positivity)
    _ = (8 * K * ((L + 1 : ℕ) : ℝ) ^ 3) * (M : ℝ) ^ (1 / 2 : ℝ) := by ring
    _ ≤ (M : ℝ) ^ ε * (M : ℝ) ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hm.le _)
    _ = _ := by rw [← Real.rpow_add hm]; congr 1; ring

theorem uniform_power_errors (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      |unsignedTotal M δ L - ((M : ℝ) - 2 * (M : ℝ) ^ δ) * (unsigned L 1 2 : ℤ)| ≤ (M : ℝ) ^ (1 / 2 + ε) ∧
      |signedTotal M δ L - ((M : ℝ) - 2 * (M : ℝ) ^ δ) * (signed L 1 2 : ℤ)| ≤ (M : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨ME, hE⟩ := uniform_real_errors C δ hδ hδ1
  obtain ⟨MP, hP⟩ := endpoint_rate C ε hε
  refine ⟨max ME MP, ?_⟩
  intro M hM L hcrit
  obtain ⟨hu, hs⟩ := hE M (by omega) L hcrit
  have hp := hP M (by omega) L hcrit
  exact ⟨hu.trans hp, hs.trans hp⟩

end PaperP1.MacroscopicLeadingUnitSums
