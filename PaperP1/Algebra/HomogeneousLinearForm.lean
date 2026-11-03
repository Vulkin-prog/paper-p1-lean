module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # A homogeneous polynomial of degree one is its literal linear coefficient form -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.HomogeneousLinearForm

open MvPolynomial

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

theorem eq_sum (f : MvPolynomial σ R) (hf : f.IsHomogeneous 1) :
    f = ∑ i, C (f.coeff (Finsupp.single i 1)) * X i := by
  classical
  apply MvPolynomial.ext
  intro d
  simp only [coeff_sum, coeff_C_mul, coeff_X]
  by_cases hd : d.degree = 1
  · have hd' : d.sum (fun _ n ↦ n) = 1 := hd
    obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp hd'
    simp only [Finsupp.single_left_inj (by decide : (1 : ℕ) ≠ 0)]
    simp
  · rw [hf.coeff_eq_zero hd]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hne : Finsupp.single i 1 ≠ d := fun h ↦ hd (h ▸ Finsupp.degree_single i 1)
    rw [ite_eq_right hne, mul_zero]

theorem eq_three (f : MvPolynomial (Fin 3) R) (hf : f.IsHomogeneous 1) :
    f = C (f.coeff (Finsupp.single 0 1)) * X 0 + C (f.coeff (Finsupp.single 1 1)) * X 1 +
      C (f.coeff (Finsupp.single 2 1)) * X 2 := by
  simpa only [Fin.sum_univ_three] using eq_sum f hf

end PaperP1.HomogeneousLinearForm
