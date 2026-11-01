module

public import PaperP1.Diophantine.BihomogeneousSwap
public import PaperP1.Diophantine.ProjectiveCurveCount

/-! # Transposition of an actual auxiliary equation of bidegree (1,1) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BilinearAuxiliary

open MvPolynomial

variable {R : Type*} [CommRing R]

def form (a b : R) : MvPolynomial (Fin 2) R := C a * X 0 + C b * X 1

def auxiliary (F G : MvPolynomial (Fin 2) R) :
    MvPolynomial (Fin 2) (MvPolynomial (Fin 2) R) := C F * X 0 + C G * X 1

theorem form_homogeneous (a b : R) : (form a b).IsHomogeneous 1 := by
  apply IsHomogeneous.add
  · simpa only [zero_add] using (isHomogeneous_C (Fin 2) a).mul (isHomogeneous_X R 0)
  · simpa only [zero_add] using (isHomogeneous_C (Fin 2) b).mul (isHomogeneous_X R 1)

theorem eval_form (a b : R) (z : Fin 2 → R) : eval z (form a b) = a * z 0 + b * z 1 := by
  simp only [form, map_add, map_mul, eval_C, eval_X]

theorem form_map {S : Type*} [CommRing S] (φ : R →+* S) (a b : R) :
    MvPolynomial.map φ (form a b) = form (φ a) (φ b) := by
  simp [form]

theorem homogeneous_linear_form (F : MvPolynomial (Fin 2) R) (hF : F.IsHomogeneous 1) :
    F = form ((PaperP1.HomogeneousCharts.chart F).coeff 1)
      ((PaperP1.HomogeneousCharts.chart F).coeff 0) := by
  have h := PaperP1.BihomogeneousSwap.binary_expansion F hF
  simpa [Fin.sum_univ_two, form, add_comm] using h

theorem auxiliary_transpose (a b c e : R) :
    MvPolynomial.commAlgEquiv R (Fin 2) (Fin 2) (auxiliary (form a b) (form c e)) =
      auxiliary (form a c) (form b e) := by
  simp only [auxiliary, form, map_add, map_mul, commAlgEquiv_C, commAlgEquiv_X,
    MvPolynomial.map_C, MvPolynomial.map_X]
  ring

theorem irreducible_transpose (a b c e : R)
    (h : Irreducible (auxiliary (form a b) (form c e))) :
    Irreducible (auxiliary (form a c) (form b e)) := by
  rw [← auxiliary_transpose]
  exact h.map (MvPolynomial.commAlgEquiv R (Fin 2) (Fin 2)).toMulEquiv

theorem form_coeff_left (a b : R) : (form a b).coeff (Finsupp.single 0 1) = a :=
  PaperP1.ProjectiveResultants.linear_coefficient_left a b

theorem form_coeff_right (a b : R) : (form a b).coeff (Finsupp.single 1 1) = b :=
  PaperP1.ProjectiveResultants.linear_coefficient_right a b

theorem form_coefficient_bound (a b : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (ha : (a.natAbs : ℝ) ≤ B) (hb : (b.natAbs : ℝ) ≤ B) :
    ∀ m, (((form a b).coeff m).natAbs : ℝ) ≤ B := by
  intro m
  by_cases h0 : m = Finsupp.single 0 1
  · subst m
    simpa only [form_coeff_left] using ha
  by_cases h1 : m = Finsupp.single 1 1
  · subst m
    simpa only [form_coeff_right] using hb
  have hz : (form a b).coeff m = 0 := by
    change (C a * X (0 : Fin 2)).coeff m + (C b * X (1 : Fin 2)).coeff m = 0
    rw [coeff_C_mul, coeff_C_mul, coeff_X, coeff_X]
    simp only [ite_eq_right (Ne.symm h0), ite_eq_right (Ne.symm h1), mul_zero, add_zero]
  simpa only [hz, Int.natAbs_zero, Nat.cast_zero] using hB

theorem good_swap {ell k : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (hC : ∀ i, (C i).IsHomogeneous k) (a b c e h : ℤ)
    (s : PaperP1.BidegreeOneFibreCount.Point) :
    PaperP1.ProjectiveCurveCount.Good C (form a b) (form c e) h s ↔
      PaperP1.ProjectiveCurveCount.Good (PaperP1.BihomogeneousSwap.coefficients (k := k) C)
        (form a c) (form b e) h s.swap := by
  have heq : s.1 0 * eval s.2 (form a b) + s.1 1 * eval s.2 (form c e) =
      s.2 0 * eval s.1 (form a c) + s.2 1 * eval s.1 (form b e) := by
    simp only [eval_form]
    ring
  simp only [PaperP1.ProjectiveCurveCount.Good, Prod.swap, PaperP1.BihomogeneousSwap.original_swap C hC,
    ← heq]
  constructor <;> rintro ⟨hp, hq, haux, horig⟩ <;> exact ⟨hq, hp, haux, horig⟩

end PaperP1.BilinearAuxiliary
