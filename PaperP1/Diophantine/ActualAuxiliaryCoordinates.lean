module

public import PaperP1.Arithmetic.ActualProjectivePairs
public import PaperP1.Asymptotics.BiformCoordinateHeight

/-! # Actual auxiliary equations in the constructed inverse integer coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualAuxiliaryCoordinates

open PaperP1.DeterminantIntegerRows PaperP1.DeterminantAuxiliaryBiform PaperP1.BiformCoefficientRecovery
open PaperP1.BiformCoordinateEquation PaperP1.ActualProjectivePairs PaperP1.TwoKernelDeterminantBoxes

theorem forms_height (a b H : ℕ) (w : Exponent a b → ℤ)
    (hH : ∀ m n, |((biform a b w).coeff m).coeff n| ≤ (H : ℤ)) :
    ∀ i m, ((forms a b w i).coeff m).natAbs ≤ H := by
  have hw := coefficient_bound_from_biform a b H w hH
  intro i m
  have hh := forms_coefficient_bound a b H w hw i m
  have hc : (((forms a b w i).coeff m).natAbs : ℤ) ≤ (H : ℤ) := by
    simpa only [Int.natCast_natAbs] using hh
  exact_mod_cast hc

theorem forms_family_nonzero (a b : ℕ) (w : Exponent a b → ℤ) (hw : biform a b w ≠ 0) :
    forms a b w ≠ 0 := by
  have hw0 : w ≠ 0 := fun h ↦ hw ((biform_zero_iff a b w).mpr h)
  obtain ⟨i, hi⟩ := forms_nonzero a b w hw0
  exact fun h ↦ hi (congrFun h i)

theorem uniform_transformed_family_height (Amax Bmax κ μ ν : ℕ) :
    ∃ κ' N₀ : ℕ, ∀ N ≥ N₀, ∀ a ≤ Amax, ∀ b ≤ Bmax,
      ∀ w : Exponent a b → ℤ,
      (∀ m n, |((biform a b w).coeff m).coeff n| ≤ ((N ^ κ : ℕ) : ℤ)) →
      ∀ A C : Matrix (Fin 2) (Fin 2) ℤ,
      (∀ i j, (A i j).natAbs ≤ N ^ μ) → (∀ i j, (C i j).natAbs ≤ N ^ ν) →
      ∀ i m, ((PaperP1.BiformLinearCoordinates.transform (b := b) A C (forms a b w) i).coeff m).natAbs ≤ N ^ κ' := by
  obtain ⟨κ', N₀, hheight⟩ := BiformCoordinateHeight.uniform_transformed_height Amax Bmax κ μ ν
  refine ⟨κ', N₀, ?_⟩
  intro N hN a ha b hb w hw A C hA hC
  have hEq := hheight N hN a ha b hb A C (forms a b w) (forms_homogeneous a b w)
    (forms_height a b (N ^ κ) w hw) hA hC
  have hrows := forms_height a b (N ^ κ')
    (weights (PaperP1.BiformLinearCoordinates.transform (b := b) A C (forms a b w))) hEq
  simpa only [forms_weights _ (PaperP1.BiformLinearCoordinates.transform_homogeneous A C _)] using hrows

theorem coordinate_zero (a b : ℕ) (w : Exponent a b → ℤ)
    (A B C D : Matrix (Fin 2) (Fin 2) ℤ) (hAB : A * B = 1) (hCD : C * D = 1) (p : Quad)
    (hp : MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1])
      ![(p.1.1 : ℤ), p.1.2] (biform a b w) = 0) :
    BidegreeOneElimination.original (PaperP1.BiformLinearCoordinates.transform (b := b) A C (forms a b w))
      (coordinates B D p).1 (coordinates B D p).2 = 0 := by
  have ho : BidegreeOneElimination.original (forms a b w) (integerPoint p).1 (integerPoint p).2 = 0 := by
    simpa only [biform_eval_original, integerPoint] using hp
  have ht := (BiformPointCoordinates.inverse_equation_zero A B C D hAB hCD (forms a b w)
    (forms_homogeneous a b w) (integerPoint p)).mpr ho
  rw [equation_evaluation _ (PaperP1.BiformLinearCoordinates.transform_homogeneous A C _)] at ht
  exact ht

end PaperP1.ActualAuxiliaryCoordinates
