module

public import PaperP1.Geometry.P3FactorSegreFieldPoint

/-! # Exact nonzero factor vectors from an actual field evaluation of the Segre quotient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3FactorSegreEvaluation

open MvPolynomial P3HomogeneousCoefficientFamily P3FactorSegreRelations P3FactorSegreGrading

variable {F : Type} [Field F] (e f : ℕ) (ε : Quotient e f →+* F)

theorem rank_one (i k : Index e) (j l : Index f) :
    ε (coordinate e f (i, j)) * ε (coordinate e f (k, l)) =
      ε (coordinate e f (i, l)) * ε (coordinate e f (k, j)) := by
  have hz : Ideal.Quotient.mk (ideal e f) (relation e f i k j l) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (relation_mem e f i k j l)
  have he := congrArg ε hz
  simpa only [relation, map_sub, map_mul, map_zero, coordinate, sub_eq_zero] using he

theorem evaluation (P : Ring e f) :
    ε (Ideal.Quotient.mk (ideal e f) P) =
      eval (fun ij ↦ ε (coordinate e f ij)) (map (Int.castRingHom F) P) := by
  have he : ε.comp (Ideal.Quotient.mk (ideal e f)) =
      eval₂Hom (Int.castRingHom F) (fun ij ↦ ε (coordinate e f ij)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro ij
      simp [coordinate]
  rw [eval_map]
  exact RingHom.congr_fun he P

theorem coefficient_evaluation (m : Index (e + f)) :
    ε (coefficient e f m) = eval (fun ij ↦ ε (coordinate e f ij))
      (map (Int.castRingHom F) (P3CoefficientMultiplication.coefficientForm e f m)) :=
  evaluation e f ε _

theorem coordinates_ne_zero (hε : (fun m ↦ ε (coefficient e f m)) ≠ 0) :
    (fun ij ↦ ε (coordinate e f ij)) ≠ 0 := by
  intro hz
  apply hε
  funext m
  rw [coefficient_evaluation, P3CoefficientMultiplication.evaluate_form]
  simp only [congr_fun hz, Pi.zero_apply, ite_self, Finset.sum_const_zero]

theorem exists_factors (hε : (fun m ↦ ε (coefficient e f m)) ≠ 0) :
    ∃ (a : Index e → F) (b : Index f → F), a ≠ 0 ∧ b ≠ 0 ∧
      P3FactorSegreFieldPoint.productVector e f a b = fun m ↦ ε (coefficient e f m) := by
  obtain ⟨a, b, ha, hb, hab⟩ := RankOneTensorFactorization.exists_factors
    (fun ij ↦ ε (coordinate e f ij)) (coordinates_ne_zero e f ε hε) (rank_one e f ε)
  refine ⟨a, b, ha, hb, ?_⟩
  have he : (fun ij ↦ ε (coordinate e f ij)) = P3FactorSegreFieldPoint.tensorVector e f a b :=
    funext hab
  funext m
  rw [coefficient_evaluation, he]
  rfl

end PaperP1.P3FactorSegreEvaluation
