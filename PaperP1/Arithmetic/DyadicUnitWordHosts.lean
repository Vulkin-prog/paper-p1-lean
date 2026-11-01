module

public import PaperP1.Arithmetic.UnitShapePatterns

/-! # Reindex the actual dyadic unit-word aggregate by literal source pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicUnitWordHosts

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedUnitCount
  PaperP1.UnitShapePatterns PaperP1.ChannelWordHosts PaperP1.DyadicEndpointPairs
  PaperP1.ActualSourceTranslations PaperP1.ChannelPlacements

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def forwardHosts (N L a b : ℕ) : ℤ :=
  ∑ p : Patterns L a b, coefficient p *
    (sourcePairs N a b L (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).card

theorem weighted_unit_hosts (N : ℕ) {L a b : ℕ} (p : Patterns L a b) (κ : ℤ) :
    (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, if HasUnit x y p then κ else 0) =
      κ * (sourcePairs N a b L (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).card := by
  have hfilter : ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter (fun xy ↦ HasUnit xy.1 xy.2 p) =
      sourcePairs N a b L (placementIndex L p.2.1.val) (placementIndex L p.2.2.val) := by
    ext xy
    simp only [mem_filter, HasUnit, mem_units, sourcePairs]
  calc
    _ = ∑ xy ∈ (dyadicBlock N) ×ˢ (dyadicBlock N), if HasUnit xy.1 xy.2 p then κ else 0 :=
      (sum_product _ _ (fun xy : ℕ × ℕ ↦ if HasUnit xy.1 xy.2 p then κ else 0)).symm
    _ = ∑ xy ∈ ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter (fun xy ↦ HasUnit xy.1 xy.2 p), κ :=
      (sum_filter _ _).symm
    _ = _ := by rw [hfilter, sum_const, nsmul_eq_mul]; ring

theorem integer_dyadic_sum (N L a b : ℕ) :
    (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, integerPatternSum a b x y L) = forwardHosts N L a b := by
  unfold integerPatternSum
  calc
    _ = ∑ x ∈ dyadicBlock N, ∑ p : Patterns L a b,
        ∑ y ∈ dyadicBlock N, if HasUnit x y p then coefficient p else 0 := by
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
    _ = ∑ p : Patterns L a b, ∑ x ∈ dyadicBlock N,
        ∑ y ∈ dyadicBlock N, if HasUnit x y p then coefficient p else 0 := sum_comm
    _ = _ := by
      unfold forwardHosts
      apply sum_congr rfl
      intro p _
      exact weighted_unit_hosts N p (coefficient p)

theorem signed_hosts_integer (N L a b : ℕ) :
    signedHosts N L a b =
      ((∑ p : Patterns L a b, coefficient p *
        ((symmetricSources N a b L (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).card : ℤ) : ℤ) : ℚ) := by
  unfold signedHosts
  rw [Int.cast_sum]
  apply sum_congr rfl
  intro p _
  simp only [patternWeight, patternSign, sourceCount, UnitShapePatterns.coefficient, Int.cast_mul, Int.cast_natCast]
  ring

theorem signed_hosts_twice_forward {N L a b : ℕ} (hN : 0 < N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) : signedHosts N L a b = 2 * (forwardHosts N L a b : ℚ) := by
  have hint : (∑ p : Patterns L a b, coefficient p *
      ((symmetricSources N a b L (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).card : ℤ)) =
        2 * forwardHosts N L a b := by
    unfold forwardHosts
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    rw [symmetric_card hN hab hlarge, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [signed_hosts_integer, hint, Int.cast_mul, Int.cast_ofNat]

end PaperP1.DyadicUnitWordHosts
