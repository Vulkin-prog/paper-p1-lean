module

public import PaperP1.Affine.Probability
public import Mathlib.Data.Finset.Card

/-! # A binary vector space of dimension at most one has one possible nonzero vector -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryRankOne

open Finset PaperP1.Affine

variable {V : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V]

theorem nonzero_eq (hrank : Module.finrank 𝔽₂ V ≤ 1) (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
  classical
  have hcard : Fintype.card V ≤ 2 := by
    rw [card_eq_two_pow_finrank]
    exact (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hrank).trans_eq (by norm_num)
  have hsmall : (univ.erase (0 : V)).card ≤ 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ]
    omega
  exact card_le_one.mp hsmall a (mem_erase.mpr ⟨ha, mem_univ _⟩) b (mem_erase.mpr ⟨hb, mem_univ _⟩)

end PaperP1.BinaryRankOne
