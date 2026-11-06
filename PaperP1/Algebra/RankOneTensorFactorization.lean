module

public import Mathlib.Tactic.FieldSimp

/-! # Literal outer-product factorization of a nonzero matrix with vanishing two-by-two minors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RankOneTensorFactorization

variable {F ι κ : Type*} [Field F]

theorem at_pivot (z : ι × κ → F) (i₀ : ι) (j₀ : κ) (hpivot : z (i₀, j₀) ≠ 0)
    (hminor : ∀ (i k : ι) (j l : κ), z (i, j) * z (k, l) = z (i, l) * z (k, j)) :
    ∃ (a : ι → F) (b : κ → F), a ≠ 0 ∧ b ≠ 0 ∧ ∀ ij, z ij = a ij.1 * b ij.2 := by
  let a : ι → F := fun i ↦ z (i, j₀)
  let b : κ → F := fun j ↦ z (i₀, j) / z (i₀, j₀)
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro hz
    exact hpivot (congrFun hz i₀)
  · intro hz
    have hh := congrFun hz j₀
    change z (i₀, j₀) / z (i₀, j₀) = 0 at hh
    rw [div_self hpivot] at hh
    exact one_ne_zero hh
  · rintro ⟨i, j⟩
    change z (i, j) = z (i, j₀) * (z (i₀, j) / z (i₀, j₀))
    apply (mul_right_cancel₀ hpivot)
    rw [mul_assoc, div_mul_cancel₀ _ hpivot]
    exact hminor i i₀ j j₀

theorem exists_factors (z : ι × κ → F) (hz : z ≠ 0)
    (hminor : ∀ (i k : ι) (j l : κ), z (i, j) * z (k, l) = z (i, l) * z (k, j)) :
    ∃ (a : ι → F) (b : κ → F), a ≠ 0 ∧ b ≠ 0 ∧ ∀ ij, z ij = a ij.1 * b ij.2 := by
  obtain ⟨ij, hij⟩ := Function.ne_iff.mp hz
  exact at_pivot z ij.1 ij.2 hij hminor

end PaperP1.RankOneTensorFactorization
