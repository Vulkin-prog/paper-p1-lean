module

public import PaperP1.Algebra.SmallIntegerKernel
public import PaperP1.Algebra.PrimitiveTripleDirection

/-! # A finite family of small integer planes has at most a constant times B^5 elements -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedIntegerPlanes

open Finset PaperP1.PrimitiveTripleDirection PaperP1.SmallIntegerKernel

def family (K B : ℕ) : Finset ((Fin 3 → ℤ) × ℤ) :=
  symmetricBox 3 (K * B) ×ˢ Icc (-((K * B ^ 2 : ℕ) : ℤ)) ((K * B ^ 2 : ℕ) : ℤ)

theorem interval_mem (W : ℕ) (z : ℤ) : z ∈ Icc (-(W : ℤ)) W ↔ z.natAbs ≤ W := by
  constructor
  · intro hz
    have hh : |z| ≤ (W : ℤ) := abs_le.mpr (mem_Icc.mp hz)
    rw [Int.abs_eq_natAbs] at hh
    exact_mod_cast hh
  · intro hz
    apply mem_Icc.mpr
    apply abs_le.mp
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hz

theorem height_le_iff (A : Fin 3 → ℤ) (W : ℕ) : height A ≤ W ↔ ∀ i, (A i).natAbs ≤ W := by
  constructor
  · intro hh i
    exact (coordinate_natAbs_le_height A i).trans hh
  · intro hh
    exact max_le (hh 0) (max_le (hh 1) (hh 2))

theorem mem_family (K B : ℕ) (A : Fin 3 → ℤ) (h : ℤ) :
    (A, h) ∈ family K B ↔ height A ≤ K * B ∧ h.natAbs ≤ K * B ^ 2 := by
  simp only [family, mem_product, symmetricBox, Fintype.mem_piFinset, interval_mem, height_le_iff]

theorem card_family (K B : ℕ) :
    (family K B).card = (2 * K * B + 1) ^ 3 * (2 * K * B ^ 2 + 1) := by
  have hc (W : ℕ) : (Icc (-(W : ℤ)) W).card = 2 * W + 1 := by rw [Int.card_Icc]; omega
  rw [family, card_product, symmetricBox_card, hc]
  ring

theorem card_bound (K B : ℕ) (hB : 1 ≤ B) : (family K B).card ≤ (2 * K + 1) ^ 4 * B ^ 5 := by
  have hfirst : 2 * K * B + 1 ≤ (2 * K + 1) * B := by nlinarith
  have hB2 : 1 ≤ B ^ 2 := by nlinarith
  have hsecond : 2 * K * B ^ 2 + 1 ≤ (2 * K + 1) * B ^ 2 := by nlinarith only [hB2]
  rw [card_family]
  calc
    _ ≤ ((2 * K + 1) * B) ^ 3 * ((2 * K + 1) * B ^ 2) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hfirst 3) hsecond
    _ = _ := by ring

end PaperP1.BoundedIntegerPlanes
