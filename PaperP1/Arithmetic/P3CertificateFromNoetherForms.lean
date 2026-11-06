module

public import PaperP1.Arithmetic.P3UniversalNoetherForms
public import PaperP1.Arithmetic.P3FiniteFieldClassEstimate
public import PaperP1.Arithmetic.UniformP3AuxiliaryFromFiniteFieldCertificate
public import PaperP1.Algebra.IntegerPolynomialEvaluationMass
public import PaperP1.Algebra.IntegerPolynomialReduction

/-! # Actual universal-form evaluation constructs the independent integer good-prime certificate and its height bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3CertificateFromNoetherForms

open MvPolynomial Finset P3HomogeneousCoefficientFamily
open IntegerPolynomialEvaluationMass
open scoped Classical

theorem budget_of_valid_forms (d : ℕ) (forms : Finset (MvPolynomial (Index d) ℤ))
    (hforms : P3UniversalNoetherForms.Valid d forms)
    (hestimate : P3FiniteFieldClassEstimate.UniformEstimate d) :
    UniformP3FiniteFieldCertificate.UniformBudget d := by
  intro η hη
  obtain ⟨K₀, hestimate⟩ := hestimate η hη
  refine ⟨familyMass forms, familyDegree forms, K₀, familyMass_pos forms, ?_⟩
  intro A hA P hgeom hhom hcoef
  let a : Index d → ℤ := fun m ↦ P.coeff m.val
  have hq := P3CoefficientFieldTransport.map_reconstruct (Int.castRingHom ℚ) d P hhom
  change map (Int.castRingHom ℚ) P = polynomial d (fun m ↦ (a m : ℚ)) at hq
  have hgeom_a : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ))
      (polynomial d (fun m ↦ (a m : ℚ)))) := by
    rw [← hq]
    exact hgeom
  obtain ⟨Φ, hΦ, hΦQ⟩ := (hforms ℚ (fun m ↦ (a m : ℚ))).mp hgeom_a
  let z : ℤ := eval a Φ
  have hevalQ := IntegerPolynomialReduction.map_evaluation (Int.castRingHom ℚ) a Φ
  change (z : ℚ) = eval (fun m ↦ (a m : ℚ)) (map (Int.castRingHom ℚ) Φ) at hevalQ
  have hz : z ≠ 0 := by
    intro hzero
    apply hΦQ
    rw [← hevalQ, hzero, Int.cast_zero]
  have hbound : z.natAbs ≤ familyMass forms * A ^ familyDegree forms :=
    family_bound forms Φ hΦ A (by omega) a (fun m ↦ hcoef m.val)
  refine ⟨z, hz, hbound, ?_⟩
  intro p hp hK hnot
  let : Fact p.Prime := ⟨hp⟩
  have hzp : (z : ZMod p) ≠ 0 := by
    intro hh
    exact hnot ((ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hh)
  have hevalp := IntegerPolynomialReduction.map_evaluation (Int.castRingHom (ZMod p)) a Φ
  change (z : ZMod p) = eval (fun m ↦ (a m : ZMod p)) (map (Int.castRingHom (ZMod p)) Φ) at hevalp
  have hΦp : eval (fun m ↦ (a m : ZMod p)) (map (Int.castRingHom (ZMod p)) Φ) ≠ 0 := by
    rw [← hevalp]
    exact hzp
  have hgeom_ap := (hforms (ZMod p) (fun m ↦ (a m : ZMod p))).mpr ⟨Φ, hΦ, hΦp⟩
  have hpmodel := P3CoefficientFieldTransport.map_reconstruct (Int.castRingHom (ZMod p)) d P hhom
  change map (Int.castRingHom (ZMod p)) P = polynomial d (fun m ↦ (a m : ZMod p)) at hpmodel
  have hgeom_p : P3FiniteFieldClassEstimate.GeometricReduction p hp P := by
    change Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) P))
    rw [hpmodel]
    exact hgeom_ap
  exact hestimate p hp hK P hhom hgeom_p

theorem uniform_budget (d : ℕ) (hforms : P3UniversalNoetherForms.ExistsForms d)
    (hestimate : P3FiniteFieldClassEstimate.UniformEstimate d) :
    UniformP3FiniteFieldCertificate.UniformBudget d := by
  obtain ⟨forms, hforms⟩ := hforms
  exact budget_of_valid_forms d forms hforms hestimate

theorem uniform_auxiliary (d : ℕ) (hforms : P3UniversalNoetherForms.ExistsForms d)
    (hestimate : P3FiniteFieldClassEstimate.UniformEstimate d) :
    UniformP3AuxiliaryHypersurface.UniformAuxiliary d :=
  UniformP3AuxiliaryFromFiniteFieldCertificate.uniform_auxiliary d (uniform_budget d hforms hestimate)

end PaperP1.P3CertificateFromNoetherForms
