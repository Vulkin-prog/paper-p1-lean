module

public import PaperP1.Algebra.FiniteGradedHilbertCoefficient
public import PaperP1.Algebra.FiniteHomogeneousModuleGenerators
public import PaperP1.Algebra.GradedPolynomialGenerators
public import PaperP1.Algebra.MvPolynomialHilbert
public import PaperP1.Algebra.WeightedVeroneseHilbertPolynomial

/-! # The actual rank of three independent finite linear parameters is twice the quadratic Hilbert coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteSurfaceParameterRank

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

local instance fieldCommSemiring (F : Type*) [Field F] : CommSemiring F :=
  (inferInstance : Field F).toCommRing.toCommSemiring
local instance polynomialRing (F σ : Type*) [Field F] : CommRing (MvPolynomial σ F) := inferInstance
local instance polynomialSemiring (F σ : Type*) [Field F] : Semiring (MvPolynomial σ F) :=
  (polynomialRing F σ).toSemiring

theorem base_hilbert (F : Type*) [Field F] :
    GradedHilbertPolynomial.IsHilbertPolynomial (homogeneousSubmodule (Fin 3) F)
      (WeightedVeroneseHilbertPolynomial.term 1 0) := by
  refine ⟨0, fun n _hn ↦ ?_⟩
  rw [WeightedVeroneseHilbertPolynomial.term_eval 1 0 n (Nat.zero_le n),
    MvPolynomialHilbert.ternary_piece_finrank]
  simp only [Nat.sub_zero, Nat.mul_one]

theorem rank_eq_twice_coefficient {F A : Type*} [Field F] [CommRing A] [Algebra F A] [IsDomain A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (g : Fin 3 → A) (hg : ∀ i, g i ∈ H 1) (hfinite : (aeval (R := F) g).Finite)
    (hinj : Function.Injective (aeval (R := F) g)) (p : Polynomial ℚ)
    (hdegree : p.natDegree ≤ 2) (hp : GradedHilbertPolynomial.IsHilbertPolynomial H p) :
    letI : Algebra (MvPolynomial (Fin 3) F) A := (aeval (R := F) g).toRingHom.toAlgebra
    (Module.finrank (MvPolynomial (Fin 3) F) A : ℚ) = 2 * p.coeff 2 := by
  let : Algebra (MvPolynomial (Fin 3) F) A := (aeval (R := F) g).toRingHom.toAlgebra
  let : Module.Finite (MvPolynomial (Fin 3) F) A := hfinite
  let f := GradedPolynomialGenerators.gradedEval H g hg
  obtain ⟨ι, hι, v, w, hv, hspan⟩ := FiniteHomogeneousModuleGenerators.exists_generators
    (A := MvPolynomial (Fin 3) F) H
  let : Fintype ι := hι
  have hc := FiniteGradedHilbertCoefficient.coefficient_eq f
    (fun r ↦ (aeval (R := F) g).commutes r) v w hv hinj hspan
    (fun n ↦ MvPolynomialHilbert.piece_finite F (Fin 3) n)
    (WeightedVeroneseHilbertPolynomial.term 1 0) p 2
    (WeightedVeroneseHilbertPolynomial.term_natDegree_le 1 0) hdegree (base_hilbert F) hp
  change p.coeff 2 = (Module.finrank (MvPolynomial (Fin 3) F) A : ℚ) *
    (WeightedVeroneseHilbertPolynomial.term 1 0).coeff 2 at hc
  rw [WeightedVeroneseHilbertPolynomial.term_coeff_two] at hc
  norm_num at hc
  linarith

end PaperP1.FiniteSurfaceParameterRank
