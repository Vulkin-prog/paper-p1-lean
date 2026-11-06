module

public import PaperP1.Arithmetic.P3UniversalNoetherFormsExistence
public import PaperP1.Arithmetic.P3FiniteFieldClassEstimate
public import PaperP1.Algebra.IntegerPolynomialEvaluationMass
public import PaperP1.Algebra.IntegerPolynomialReduction

/-! # Unconditional polynomial-height good-reduction certificates in every degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3UniversalGoodReduction

open MvPolynomial P3HomogeneousCoefficientFamily IntegerPolynomialEvaluationMass
open scoped Classical

def Certificate (P : MvPolynomial (Fin 4) ℤ) (z : ℤ) : Prop :=
  ∀ (F : Type) [Field F], (z : F) ≠ 0 →
    Irreducible (map (algebraMap F (AlgebraicClosure F)) (map (Int.castRingHom F) P))

theorem form_evaluation (d : ℕ) (forms : Finset (MvPolynomial (Index d) ℤ))
    (hforms : P3UniversalNoetherForms.Valid d forms)
    (P : MvPolynomial (Fin 4) ℤ) (hP : P.IsHomogeneous d)
    (Φ : MvPolynomial (Index d) ℤ) (hΦ : Φ ∈ forms) :
    Certificate P (eval (fun m : Index d ↦ P.coeff m.val) Φ) := by
  intro F _ hz
  let a : Index d → ℤ := fun m ↦ P.coeff m.val
  have he := IntegerPolynomialReduction.map_evaluation (Int.castRingHom F) a Φ
  change ((eval a Φ : ℤ) : F) = eval (fun m ↦ (a m : F)) (map (Int.castRingHom F) Φ) at he
  have hn : eval (fun m ↦ (a m : F)) (map (Int.castRingHom F) Φ) ≠ 0 := by
    rw [← he]
    exact hz
  have hirr := (hforms F (fun m ↦ (a m : F))).mpr ⟨Φ, hΦ, hn⟩
  have hp := P3CoefficientFieldTransport.map_reconstruct (Int.castRingHom F) d P hP
  change map (Int.castRingHom F) P = polynomial d (fun m ↦ (a m : F)) at hp
  rw [hp]
  exact hirr

theorem bounded_from_valid_forms (d : ℕ) (forms : Finset (MvPolynomial (Index d) ℤ))
    (hforms : P3UniversalNoetherForms.Valid d forms) (A : ℕ) (hA : 0 < A)
    (P : MvPolynomial (Fin 4) ℤ) (hP : P.IsHomogeneous d)
    (hgeom : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) P)))
    (hcoef : ∀ m, |P.coeff m| ≤ (A : ℤ)) :
    ∃ z : ℤ, z ≠ 0 ∧ z.natAbs ≤ familyMass forms * A ^ familyDegree forms ∧ Certificate P z := by
  let a : Index d → ℤ := fun m ↦ P.coeff m.val
  have hq := P3CoefficientFieldTransport.map_reconstruct (Int.castRingHom ℚ) d P hP
  change map (Int.castRingHom ℚ) P = polynomial d (fun m ↦ (a m : ℚ)) at hq
  have hgeom_a : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ))
      (polynomial d (fun m ↦ (a m : ℚ)))) := by rw [← hq]; exact hgeom
  obtain ⟨Φ, hΦ, hΦQ⟩ := (hforms ℚ (fun m ↦ (a m : ℚ))).mp hgeom_a
  let z : ℤ := eval a Φ
  have he := IntegerPolynomialReduction.map_evaluation (Int.castRingHom ℚ) a Φ
  change (z : ℚ) = eval (fun m ↦ (a m : ℚ)) (map (Int.castRingHom ℚ) Φ) at he
  have hz : z ≠ 0 := by
    intro hzero
    apply hΦQ
    rw [← he]
    change (z : ℚ) = 0
    rw [hzero, Int.cast_zero]
  exact ⟨z, hz, family_bound forms Φ hΦ A (by omega) a (fun m ↦ hcoef m.val),
    form_evaluation d forms hforms P hP Φ hΦ⟩

theorem bounded_certificate (d : ℕ) :
    ∃ T N : ℕ, 0 < T ∧ ∀ A : ℕ, 0 < A → ∀ P : MvPolynomial (Fin 4) ℤ,
      P.IsHomogeneous d →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) P)) →
      (∀ m, |P.coeff m| ≤ (A : ℤ)) →
      ∃ z : ℤ, z ≠ 0 ∧ z.natAbs ≤ T * A ^ N ∧ Certificate P z := by
  obtain ⟨forms, hforms⟩ := P3UniversalNoetherFormsExistence.exists_forms d
  exact ⟨familyMass forms, familyDegree forms, familyMass_pos forms,
    bounded_from_valid_forms d forms hforms⟩

theorem geometric_reduction (P : MvPolynomial (Fin 4) ℤ) (z : ℤ) (hz : Certificate P z)
    (p : ℕ) (hp : p.Prime) (hnot : ¬ (p : ℤ) ∣ z) :
    P3FiniteFieldClassEstimate.GeometricReduction p hp P := by
  let : Fact p.Prime := ⟨hp⟩
  apply hz (ZMod p)
  intro hh
  exact hnot ((ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hh)

theorem exact_degree (d : ℕ) (P : MvPolynomial (Fin 4) ℤ) (hP : P.IsHomogeneous d)
    (z : ℤ) (hz : Certificate P z) (p : ℕ) (hp : p.Prime) (hnot : ¬ (p : ℤ) ∣ z) :
    (map (Int.castRingHom (ZMod p)) P).totalDegree = d := by
  let : Fact p.Prime := ⟨hp⟩
  have hg := geometric_reduction P z hz p hp hnot
  have hn : map (Int.castRingHom (ZMod p)) P ≠ 0 := by
    intro hh
    exact hg.ne_zero (by rw [hh, map_zero])
  exact (hP.map _).totalDegree hn

end PaperP1.P3UniversalGoodReduction
