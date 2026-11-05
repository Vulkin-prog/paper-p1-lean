module

public import PaperP1.Algebra.FinitePlaneBezout
public import PaperP1.Algebra.BivariateTotalDegreeChart
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Finite and infinite common populations in actual two-variable coordinates

The coordinate chart retains both the total degree and every actual point.
An infinite population forces divisibility; smaller-degree nonzero equations
cannot vanish identically on it.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MvPlaneBezout

open MvPolynomial Finset Set

variable {F : Type*} [Field F] [Infinite F]

theorem common_points_card (P Q : MvPolynomial (Fin 2) F) (hP : Irreducible P)
    (hnot : ¬P ∣ Q) (S : Finset (Fin 2 → F))
    (hS : ∀ z ∈ S, eval z P = 0 ∧ eval z Q = 0) :
    S.card ≤ P.totalDegree * Q.totalDegree := by
  classical
  let e := BivariateTotalDegreeChart.chart F
  let π : (Fin 2 → F) → F × F := fun z ↦ (z 1, z 0)
  have hinj : Function.Injective π := by
    intro z w he
    funext i
    fin_cases i
    · exact congrArg Prod.snd he
    · exact congrArg Prod.fst he
  have heval (R : MvPolynomial (Fin 2) F) (z : Fin 2 → F) :
      (e R).evalEval (π z).1 (π z).2 = eval z R := by
    change (BivariateTotalDegreeChart.chart F R).evalEval (z 1) (z 0) = eval z R
    have hv : Fin.cons (z 0) (fun _ : Fin 1 ↦ z 1) = z := by
      funext i
      fin_cases i <;> rfl
    rw [BivariateTotalDegreeChart.chart_evaluation, hv]
  have hP' : Irreducible (e P) := (MulEquiv.irreducible_iff e.toRingEquiv.toMulEquiv).mpr hP
  have hnot' : ¬e P ∣ e Q := by
    rintro ⟨A, hA⟩
    apply hnot
    refine ⟨e.symm A, ?_⟩
    simpa only [map_mul, AlgEquiv.symm_apply_apply] using congrArg e.symm hA
  have hc := FinitePlaneBezout.common_points_card (e P) (e Q) hP' hnot' (S.image π) (by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    rw [heval P w, heval Q w]
    exact hS w hw)
  have hDP : PlaneCurvePointCount.degree (e P) = P.totalDegree := BivariateTotalDegreeChart.chart_degree P
  have hDQ : PlaneCurvePointCount.degree (e Q) = Q.totalDegree := BivariateTotalDegreeChart.chart_degree Q
  rw [Finset.card_image_of_injective _ hinj, hDP, hDQ] at hc
  exact hc

theorem dvd_of_infinite_common_zeros (P Q : MvPolynomial (Fin 2) F) (hP : Irreducible P)
    (S : Set (Fin 2 → F)) (hS : S.Infinite) (hzero : ∀ z ∈ S, eval z P = 0 ∧ eval z Q = 0) :
    P ∣ Q := by
  classical
  by_contra hnot
  obtain ⟨T, hT, hcard⟩ := hS.exists_subset_card_eq (P.totalDegree * Q.totalDegree + 1)
  have hc := common_points_card P Q hP hnot T (fun z hz ↦ hzero z (hT hz))
  omega

theorem exists_nonzero_on_curve (P Q : MvPolynomial (Fin 2) F) (hP : Irreducible P)
    (hQ : Q ≠ 0) (hdegree : Q.totalDegree < P.totalDegree)
    (S : Set (Fin 2 → F)) (hS : S.Infinite) (hzero : ∀ z ∈ S, eval z P = 0) :
    ∃ z ∈ S, eval z Q ≠ 0 := by
  by_contra hbad
  push Not at hbad
  have hdiv := dvd_of_infinite_common_zeros P Q hP S hS (fun z hz ↦ ⟨hzero z hz, hbad z hz⟩)
  have hd := totalDegree_le_of_dvd_of_isDomain hdiv hQ
  omega

end PaperP1.MvPlaneBezout
