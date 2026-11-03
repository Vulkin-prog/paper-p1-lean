module

public import PaperP1.Arithmetic.DyadicUnitWordHosts

/-! # Literal unsigned unit words and their dyadic host aggregate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnsignedUnitWordHosts

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedUnitCount
  PaperP1.UnitShapePatterns PaperP1.ChannelWordHosts PaperP1.DyadicUnitWordHosts
  PaperP1.DyadicEndpointPairs PaperP1.ActualSourceTranslations

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def integerPatternSum (a b x y L : ℕ) : ℤ :=
  ∑ p : Patterns L a b, if HasUnit x y p then ChannelSumIdentity.weight p.1.val else 0

def forwardHosts (N L a b : ℕ) : ℤ :=
  ∑ p : Patterns L a b, ChannelSumIdentity.weight p.1.val *
    (sourcePairs N a b L (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).card

theorem shape_sum (a b x y L : ℕ) :
    (∑ s : PaperP1.SelectedUnitWords.Shapes a b x y L, ChannelSumIdentity.weight s.1.val) =
      integerPatternSum a b x y L := by
  calc
    _ = ∑ p : {p : Patterns L a b // HasUnit x y p}, ChannelSumIdentity.weight p.val.1.val := by
      apply Fintype.sum_equiv (patternEquiv a b x y L)
      intro s
      rfl
    _ = _ := by
      unfold integerPatternSum
      symm
      rw [← sum_filter]
      exact sum_subtype _ (by intro p; simp only [mem_filter, mem_univ, true_and])
        (fun p : Patterns L a b ↦ ChannelSumIdentity.weight p.1.val)

theorem integer_dyadic_sum (N L a b : ℕ) :
    (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, integerPatternSum a b x y L) =
      forwardHosts N L a b := by
  unfold integerPatternSum
  calc
    _ = ∑ x ∈ dyadicBlock N, ∑ p : Patterns L a b,
        ∑ y ∈ dyadicBlock N, if HasUnit x y p then ChannelSumIdentity.weight p.1.val else 0 := by
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
    _ = ∑ p : Patterns L a b, ∑ x ∈ dyadicBlock N,
        ∑ y ∈ dyadicBlock N, if HasUnit x y p then ChannelSumIdentity.weight p.1.val else 0 := sum_comm
    _ = _ := by
      unfold forwardHosts
      apply sum_congr rfl
      intro p _
      exact weighted_unit_hosts N p (ChannelSumIdentity.weight p.1.val)

theorem unsigned_hosts_integer (N L a b : ℕ) :
    unsignedHosts N L a b =
      ((∑ p : Patterns L a b, ChannelSumIdentity.weight p.1.val *
        ((symmetricSources N a b L (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).card : ℤ) : ℤ) : ℚ) := by
  unfold unsignedHosts
  rw [Int.cast_sum]
  apply sum_congr rfl
  intro p _
  simp only [patternWeight, sourceCount, Int.cast_mul, Int.cast_natCast]

theorem unsigned_hosts_twice_forward {N L a b : ℕ} (hN : 0 < N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) :
    unsignedHosts N L a b = 2 * (forwardHosts N L a b : ℚ) := by
  have hint : (∑ p : Patterns L a b, ChannelSumIdentity.weight p.1.val *
      ((symmetricSources N a b L (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).card : ℤ)) =
        2 * forwardHosts N L a b := by
    unfold forwardHosts
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    rw [symmetric_card hN hab hlarge, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [unsigned_hosts_integer, hint, Int.cast_mul, Int.cast_ofNat]

end PaperP1.UnsignedUnitWordHosts
