module

public import PaperP1.Model.FiniteRademacher
public import PaperP1.Coding.LocalDefectBound

/-! # The exact number of prime bits and the weight of every finite cylinder atom -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeCylinderSize

open PaperP1.Model PaperP1.DefectCounting PaperP1.LocalDefectBound

def primeEquiv (M : ℕ) : PrimeUpTo M ≃ smallPrimesUpTo M where
  toFun p := ⟨p.val.val, mem_smallPrimesUpTo.mpr ⟨p.property, by have h := p.val.isLt; omega⟩⟩
  invFun p := ⟨⟨p.val, by have h := (mem_smallPrimesUpTo.mp p.property).2; omega⟩,
    (mem_smallPrimesUpTo.mp p.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem prime_card (M : ℕ) : Fintype.card (PrimeUpTo M) = primeCount M := by
  rw [Fintype.card_congr (primeEquiv M), Fintype.card_coe]
  rfl

theorem sample_card (M : ℕ) : Fintype.card (SampleSpace M) = 2 ^ primeCount M := by
  simp only [SampleSpace, Fintype.card_fun, ZMod.card, prime_card]

theorem atom_weight (M : ℕ) (σ : SampleSpace M) :
    (cylinderProbability M).weight σ = (2 ^ primeCount M : ℝ)⁻¹ := by
  change (Fintype.card (SampleSpace M) : ℝ)⁻¹ = _
  rw [sample_card, Nat.cast_pow, Nat.cast_ofNat]

end PaperP1.PrimeCylinderSize
