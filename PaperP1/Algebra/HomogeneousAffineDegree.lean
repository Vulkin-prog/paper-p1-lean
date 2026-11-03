module

public import PaperP1.Algebra.HomogeneousAffineLineClassification
public import Mathlib.Tactic.FinCases

/-! # Both literal affine partial degrees are bounded by the homogeneous plane-equation degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousAffineDegree

open Polynomial PaperP1.NativeAffineChart PaperP1.HomogeneousAffineLineClassification
  PaperP1.TrivariatePolynomialEquiv

variable {F : Type*} [Field F]

theorem degreeY_le (f : MvPolynomial (Fin 3) F) {e : ℕ} (hf : f.IsHomogeneous e) :
    (specialization F f).natDegree ≤ e := by
  have hmap : (specialization F f).natDegree ≤ (threeEquiv F f).natDegree := natDegree_map_le
  exact hmap.trans ((threeEquiv_natDegree F f).trans_le
    ((MvPolynomial.degreeOf_le_totalDegree f 0).trans hf.totalDegree_le))

theorem specialization_swap (f : MvPolynomial (Fin 3) F) :
    Bivariate.swap (specialization F f) =
      specialization F (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) f) := by
  have h : (Bivariate.swap (R := F)).toRingHom.comp (specialization F) =
      (specialization F).comp (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change Bivariate.swap (specialization F (MvPolynomial.C a)) =
        specialization F (MvPolynomial.rename (Equiv.swap (0 : Fin 3) 1) (MvPolynomial.C a))
      rw [MvPolynomial.rename_C, specialization_C, Bivariate.swap_C_C]
    · intro i
      have hswap2 : Equiv.swap (0 : Fin 3) 1 (2 : Fin 3) = 2 :=
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      fin_cases i <;> simp [RingHom.comp_apply, MvPolynomial.rename_X, specialization_X,
        specialization_Y, NativeVeroneseAffineIdeal.specialization_Z, Bivariate.swap_X,
        Bivariate.swap_Y, map_one, hswap2]
  exact RingHom.congr_fun h f

theorem degreeX_le (f : MvPolynomial (Fin 3) F) {e : ℕ} (hf : f.IsHomogeneous e) :
    (Bivariate.swap (specialization F f)).natDegree ≤ e := by
  rw [specialization_swap]
  exact degreeY_le _ hf.rename_isHomogeneous

theorem partial_degrees_le (f : MvPolynomial (Fin 3) F) {e : ℕ} (hf : f.IsHomogeneous e) :
    (Bivariate.swap (specialization F f)).natDegree ≤ e ∧ (specialization F f).natDegree ≤ e :=
  ⟨degreeX_le f hf, degreeY_le f hf⟩

end PaperP1.HomogeneousAffineDegree
