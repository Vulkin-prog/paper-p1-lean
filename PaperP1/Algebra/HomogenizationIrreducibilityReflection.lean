module

public import PaperP1.Algebra.ComplexProjectiveIrreducibility

/-! # Irreducibility is reflected by full-degree homogenization

This also identifies the exact affine content of the actual `Geometric`
predicate, rather than only supplying its previously proved sufficient test.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogenizationIrreducibilityReflection

open Polynomial PaperP1.BivariateIrreducibleHomogenization

variable {R : Type*} [CommRing R] [IsDomain R]

theorem homogenize_irreducible_iff (P : R[X]) :
    Irreducible (P.homogenize P.natDegree) ↔ Irreducible P := by
  refine ⟨?_, PaperP1.IrreducibleHomogenization.homogenize_irreducible P⟩
  intro hH
  have hp : P ≠ 0 := by
    intro hz
    apply hH.ne_zero
    simp only [hz, Polynomial.homogenize_zero]
  refine ⟨?_, ?_⟩
  · intro hu
    obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hu
    apply hH.1
    simpa only [natDegree_C, Polynomial.homogenize_C, pow_zero, mul_one] using
      hc.map (MvPolynomial.C : R →+* MvPolynomial (Fin 2) R)
  · intro A B hAB
    have hab : A * B ≠ 0 := by rw [← hAB]; exact hp
    obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp hab
    have he : P.homogenize P.natDegree = A.homogenize A.natDegree * B.homogenize B.natDegree := by
      rw [hAB, Polynomial.natDegree_mul ha hb, Polynomial.homogenize_mul _ _ le_rfl le_rfl]
    rcases hH.2 he with hu | hu
    · left
      have hh := hu.map (MvPolynomial.aeval (R := R) ![(Polynomial.X : R[X]), 1]).toRingHom
      change IsUnit (MvPolynomial.aeval ![(Polynomial.X : R[X]), 1] (A.homogenize A.natDegree)) at hh
      simpa only [Polynomial.aeval_homogenize_X_one A le_rfl] using hh
    · right
      have hh := hu.map (MvPolynomial.aeval (R := R) ![(Polynomial.X : R[X]), 1]).toRingHom
      change IsUnit (MvPolynomial.aeval ![(Polynomial.X : R[X]), 1] (B.homogenize B.natDegree)) at hh
      simpa only [Polynomial.aeval_homogenize_X_one B le_rfl] using hh

theorem bihomogenize_irreducible_iff (P : R[X][X]) (hp : P ≠ 0) :
    Irreducible (bihomogenize P) ↔ Irreducible P := by
  refine ⟨?_, bihomogenize_irreducible P⟩
  intro hh
  unfold bihomogenize at hh
  rw [← reorder_homogenize_degree P hp] at hh
  have hfirst := (homogenize_irreducible_iff (reorder R (P.homogenize P.natDegree))).mp hh
  have hpfirst := (MulEquiv.irreducible_iff (reorder R)).mp hfirst
  exact (homogenize_irreducible_iff P).mp hpfirst

theorem geometric_iff_affine (G : ℤ[X][X]) (hG : G ≠ 0) :
    PaperP1.GeometricFactorSwap.Geometric G ↔
      Irreducible (PaperP1.ComplexProjectiveIrreducibility.complexAffine G) := by
  have hp : PaperP1.ComplexProjectiveIrreducibility.complexAffine G ≠ 0 := by
    intro hz
    apply hG
    ext i j
    have hc := congrArg (fun P : ℂ[X][X] ↦ (P.coeff i).coeff j) hz
    rw [PaperP1.ComplexProjectiveIrreducibility.coefficient_cast, coeff_zero, coeff_zero] at hc
    exact_mod_cast hc
  unfold PaperP1.GeometricFactorSwap.Geometric
  rw [PaperP1.ComplexProjectiveIrreducibility.projective_identity]
  exact bihomogenize_irreducible_iff _ hp

end PaperP1.HomogenizationIrreducibilityReflection
