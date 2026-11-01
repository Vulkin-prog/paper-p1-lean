module

public import PaperP1.Model.SelectedUnitFourierEnumeration
public import PaperP1.Arithmetic.DyadicUnitWordHosts

/-! # The actual signed unit Fourier sum over dyadic hosts has main term N*w*S -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicUnitFourierAggregate

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedUnitCount
  PaperP1.UnitShapePatterns PaperP1.ChannelWordHosts PaperP1.DyadicUnitWordHosts
  PaperP1.PrivateUnitCovariance PaperP1.SelectedUnitFourierEnumeration

local instance dyadicUnitFourierPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem pair_pattern_sum {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) : signedUnitSum a b x y L = (integerPatternSum a b x y L : ℝ) := by
  rw [signed_unit_enumeration ha hb hab hx hy, shape_sum]

theorem dyadic_unit_sum {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, signedUnitSum a b x y L) = (forwardHosts N L a b : ℝ) := by
  calc
    _ = ∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, (integerPatternSum a b x y L : ℝ) := by
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      exact pair_pattern_sum ha hb hab (by have := (mem_Ico.mp hx).1; omega)
        (by have := (mem_Ico.mp hy).1; omega)
    _ = ((∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, integerPatternSum a b x y L : ℤ) : ℝ) := by
      simp only [Int.cast_sum]
    _ = _ := congrArg (fun z : ℤ ↦ (z : ℝ)) (integer_dyadic_sum N L a b)

theorem symmetric_unit_sum {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) :
    2 * (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, signedUnitSum a b x y L) =
      (signedHosts N L a b : ℝ) := by
  rw [dyadic_unit_sum hN ha (ha.trans hab) hcop]
  have h := congrArg (fun q : ℚ ↦ (q : ℝ)) (signed_hosts_twice_forward (by omega : 0 < N) hab hlarge)
  norm_num only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast] at h
  exact h.symm

theorem finite_signed_sum_error {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) :
    |2 * (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, signedUnitSum a b x y L) -
      (N : ℝ) * (ActualSourceTranslations.coefficient a b : ℝ) * (ChannelSumIdentity.signed L a b : ℤ)| ≤
        6 * ((L + 1 : ℕ) : ℝ) * (ChannelSumIdentity.unsigned L a b : ℤ) := by
  have hQ := ChannelWordHosts.signed_error hN ha hab hinterior hcop hlarge
  have hR := (Rat.cast_le (K := ℝ)).mpr hQ
  norm_num only [Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_intCast, Rat.cast_ofNat] at hR
  rw [← symmetric_unit_sum hN ha hab hcop hlarge] at hR
  exact hR

end PaperP1.DyadicUnitFourierAggregate
