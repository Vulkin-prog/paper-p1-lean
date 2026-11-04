module

public import PaperP1.Algebra.BivariateEvaluation
public import PaperP1.Algebra.IrreduciblePointFactor

/-! # A bounded finite family of nonconstant integer factors covers all rational zeros -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerBivariateFactorCover

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateEvaluation

def degreeSum (P : ℤ[X][X]) : ℕ := degreeX P + degreeY P

theorem degreeSum_mul (P Q : ℤ[X][X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    degreeSum (P * Q) = degreeSum P + degreeSum Q := by
  have hsp : Bivariate.swap P ≠ 0 := by
    intro h
    apply hP
    exact (Bivariate.swap (R := ℤ)).injective (by simpa only [map_zero] using h)
  have hsq : Bivariate.swap Q ≠ 0 := by
    intro h
    apply hQ
    exact (Bivariate.swap (R := ℤ)).injective (by simpa only [map_zero] using h)
  simp only [degreeSum, degreeX, degreeY, map_mul, natDegree_mul hP hQ, natDegree_mul hsp hsq]
  omega

theorem unit_degreeSum (P : ℤ[X][X]) (hP : IsUnit P) : degreeSum P = 0 := by
  have hs : IsUnit (Bivariate.swap P) := hP.map (Bivariate.swap (R := ℤ)).toRingHom
  simp only [degreeSum, degreeX, degreeY, natDegree_eq_zero_of_isUnit hP,
    natDegree_eq_zero_of_isUnit hs, zero_add]

theorem constant_of_degreeSum_zero (P : ℤ[X][X]) (hP : degreeSum P = 0) :
    P = Polynomial.C (Polynomial.C ((P.coeff 0).coeff 0)) := by
  have hy : P.natDegree = 0 := by unfold degreeSum degreeY at hP; omega
  have hx : degreeX P = 0 := by unfold degreeSum at hP; omega
  have hrow : (P.coeff 0).natDegree = 0 := by
    have h := natDegree_coeff_le_degreeX P 0
    omega
  exact (eq_C_of_natDegree_eq_zero hy).trans (congrArg Polynomial.C (eq_C_of_natDegree_eq_zero hrow))

theorem no_rational_zero_of_degreeSum_zero (P : ℤ[X][X]) (hP : P ≠ 0) (hd : degreeSum P = 0)
    (x y : ℚ) : evaluate x y P ≠ 0 := by
  have hc := constant_of_degreeSum_zero P hd
  have hz : (P.coeff 0).coeff 0 ≠ 0 := by
    intro h
    apply hP
    rw [hc, h]
    simp
  have hq : (((P.coeff 0).coeff 0 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hz
  rw [hc]
  simpa only [evaluate, coe_eval₂RingHom, eval₂_C, Int.coe_castRingHom] using hq

theorem exists_finite_cover (P : ℤ[X][X]) (hP : P ≠ 0) :
    ∃ F : Finset ℤ[X][X], F.card ≤ degreeSum P ∧
      (∀ G ∈ F, Irreducible G ∧ G ∣ P ∧ 0 < degreeSum G) ∧
      ∀ x y : ℚ, evaluate x y P = 0 → ∃ G ∈ F, evaluate x y G = 0 := by
  classical
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hP rfl).elim
  | unit u hu =>
    refine ⟨∅, by simp, by simp, ?_⟩
    intro x y hz
    exact ((hu.map (evaluate x y)).ne_zero hz).elim
  | mul a i ha hi ih =>
    obtain ⟨F, hFcard, hF, hcover⟩ := ih ha
    have hdegrees := degreeSum_mul i a hi.ne_zero ha
    by_cases hd : degreeSum i = 0
    · refine ⟨F, by omega, ?_, ?_⟩
      · intro G hG
        have hg := hF G hG
        exact ⟨hg.1, dvd_mul_of_dvd_right hg.2.1 i, hg.2.2⟩
      · intro x y hz
        rw [map_mul] at hz
        exact hcover x y ((mul_eq_zero.mp hz).resolve_left (no_rational_zero_of_degreeSum_zero i hi.ne_zero hd x y))
    · have hdpos : 0 < degreeSum i := by omega
      refine ⟨insert i F, (card_insert_le _ _).trans (by omega), ?_, ?_⟩
      · intro G hG
        rcases mem_insert.mp hG with rfl | hG
        · exact ⟨hi, ⟨a, rfl⟩, hdpos⟩
        · have hg := hF G hG
          exact ⟨hg.1, dvd_mul_of_dvd_right hg.2.1 i, hg.2.2⟩
      · intro x y hz
        rw [map_mul] at hz
        rcases mul_eq_zero.mp hz with hz | hz
        · exact ⟨i, mem_insert_self _ _, hz⟩
        · obtain ⟨G, hG, hzero⟩ := hcover x y hz
          exact ⟨G, mem_insert_of_mem hG, hzero⟩

end PaperP1.IntegerBivariateFactorCover
