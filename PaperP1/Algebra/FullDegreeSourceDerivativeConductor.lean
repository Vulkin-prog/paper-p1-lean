module

public import PaperP1.Algebra.FullDegreeAffineSourceField
public import PaperP1.Algebra.PrimitiveDerivativeConductor
public import PaperP1.Algebra.MonicResultantSpecialization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.CharP.Algebra

/-! # An actual monic full-degree source equation supplies its literal derivative conductor

The generic field, source domain, fraction identification, primitive coordinate
and separability are proved from the literal polynomial relation. In positive
characteristic, a degree smaller than the characteristic supplies separability.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FullDegreeSourceDerivativeConductor
open Polynomial PaperP1.LocalizedAffineQuadraticSource PaperP1.AffinePowerParameterFractionField
variable (F : Type*) [Field F] (D : ℕ) (hD : 0 < D) (s : List (Base F))

theorem fraction_irreducible (P : (Parameters F)[X]) (hmonic : P.Monic) (hP : Irreducible P) :
    Irreducible (P.map (algebraMap (Parameters F) (ParameterField F))) :=
  (hmonic.isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := ParameterField F)).mp hP

theorem fraction_degree (P : (Parameters F)[X]) :
    (P.map (algebraMap (Parameters F) (ParameterField F))).natDegree = P.natDegree :=
  Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective (Parameters F) (ParameterField F)) P

theorem generic_relation (P : (Parameters F)[X]) (y : Source F s)
    (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0) :
    letI := genericAlgebra F D hD s
    Polynomial.aeval (injection F s y) (P.map (algebraMap (Parameters F) (ParameterField F))) = 0 := by
  let := sourceAlgebra F D s
  let := genericAlgebra F D hD s
  have hc : (algebraMap (ParameterField F) (Generic F s)).comp
      (algebraMap (Parameters F) (ParameterField F)) =
      (injection F s).comp (algebraMap (Parameters F) (Source F s)) := by
    apply RingHom.ext
    intro r
    exact (parameter_compatibility F D hD s r).symm
  have hh := Polynomial.map_aeval_eq_aeval_map hc P y
  rw [hy, map_zero] at hh
  exact hh.symm

theorem separable_of_degree (p : ℕ) [CharP F p] (P : (Parameters F)[X])
    (hmonic : P.Monic) (hP : Irreducible P) (hpos : 0 < P.natDegree) (hlt : P.natDegree < p) :
    (P.map (algebraMap (Parameters F) (ParameterField F))).Separable := by
  let : CharP (ParameterField F) p := charP_of_injective_ringHom
    (f := algebraMap F (ParameterField F)) (algebraMap F (ParameterField F)).injective p
  apply (Polynomial.separable_iff_derivative_ne_zero (fraction_irreducible F P hmonic hP)).mpr
  apply PaperP1.MonicResultantSpecialization.monic_derivative_ne_zero p _ (hmonic.map _)
  · rwa [fraction_degree]
  · rwa [fraction_degree]

include hD in
theorem conductor (P : (Parameters F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (hsep : (P.map (algebraMap (Parameters F) (ParameterField F))).Separable)
    (y : Source F s) (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0)
    (hd : 2 ^ s.length * D ^ 2 ≤ P.natDegree) :
    letI := sourceAlgebra F D s
    ∀ a : Source F s, Polynomial.aeval y P.derivative * a ∈ Algebra.adjoin (Parameters F) {y} := by
  let := sourceAlgebra F D s
  let := genericAlgebra F D hD s
  let Q := P.map (algebraMap (Parameters F) (ParameterField F))
  have hQm : Q.Monic := hmonic.map _
  have hQi : Irreducible Q := fraction_irreducible F P hmonic hP
  have hQy : Polynomial.aeval (injection F s y) Q = 0 := generic_relation F D hD s P y hy
  have hQd : 2 ^ s.length * D ^ 2 ≤ Q.natDegree := by
    rw [fraction_degree]
    exact hd
  let : IsDomain (Source F s) :=
    PaperP1.FullDegreeAffineSourceField.source_isDomain F D hD s Q hQm hQi y hQy hQd
  let := (PaperP1.FullDegreeAffineSourceField.generic_isField F D hD s Q hQm hQi y hQy hQd).toField
  let : Algebra (Source F s) (Generic F s) := (injection F s).toAlgebra
  let : Algebra (Parameters F) (Generic F s) :=
    Algebra.compHom (Generic F s) (algebraMap (Parameters F) (ParameterField F))
  let : IsScalarTower (Parameters F) (ParameterField F) (Generic F s) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let : IsScalarTower (Parameters F) (Source F s) (Generic F s) :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ (parameter_compatibility F D hD s r).symm)
  let : IsFractionRing (Source F s) (Generic F s) :=
    PaperP1.FullDegreeAffineSourceField.fraction_ring F D hD s Q hQm hQi y hQy hQd
  let : Module.Finite (ParameterField F) (Generic F s) := generic_finite F D hD s
  let : Module.Finite (Parameters F) (Source F s) := source_finite F D hD s
  let : Algebra.IsSeparable (ParameterField F) (Generic F s) :=
    PaperP1.FullDegreeAffineSourceField.separable F D hD s Q hQm hQi hsep y hQy hQd
  have hmin : minpoly (Parameters F) y = P := by
    apply Polynomial.map_injective (algebraMap (Parameters F) (ParameterField F))
      (IsFractionRing.injective (Parameters F) (ParameterField F))
    have hh := minpoly.isIntegrallyClosed_eq_field_fractions (ParameterField F) (Generic F s)
      (IsIntegral.of_finite (Parameters F) y)
    exact hh.symm.trans (PaperP1.FullDegreeAffineSourceField.minimal_polynomial F D hD s Q hQm hQi y hQy)
  have hprim := PaperP1.FullDegreeAffineSourceField.primitive_intermediate F D hD s Q hQm hQi y hQy hQd
  have hh := PaperP1.PrimitiveDerivativeConductor.source_finite
    (R := Parameters F) (K := ParameterField F) (L := Generic F s) y hprim
  rw [hmin] at hh
  exact hh

include hD in
theorem conductor_in_characteristic (p : ℕ) [CharP F p]
    (P : (Parameters F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : Source F s) (hy : letI := sourceAlgebra F D s; Polynomial.aeval y P = 0)
    (hd : 2 ^ s.length * D ^ 2 ≤ P.natDegree) (hlt : P.natDegree < p) :
    letI := sourceAlgebra F D s
    ∀ a : Source F s, Polynomial.aeval y P.derivative * a ∈ Algebra.adjoin (Parameters F) {y} := by
  have hpos : 0 < P.natDegree := (by positivity : 0 < 2 ^ s.length * D ^ 2).trans_le hd
  exact conductor F D hD s P hmonic hP (separable_of_degree F p P hmonic hP hpos hlt) y hy hd

end PaperP1.FullDegreeSourceDerivativeConductor
