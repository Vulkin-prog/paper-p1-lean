module

public import PaperP1.Arithmetic.QuadraticDegreeUniformFieldCount

/-! # The absolute quadratic-degree plane count over every characteristic-zero field, including degree one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticAllDegreePlaneCount

universe u

open DegreeUniformAffineParameters QuadraticDegreeUniformFieldCount

theorem grid_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 0 < D → 1 ≤ N →
    ∀ (F : Type*) [Field F] [CharZero F], ∀ P : Polynomial (Polynomial F),
    PlaneCurvePointCount.degree P = D → Irreducible P →
    ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ C * profile D N := by
  obtain ⟨C₀, hC₀, hcount⟩ := QuadraticDegreeUniformFieldCount.field_count
  refine ⟨3 + C₀, by positivity, ?_⟩
  intro D N hD hN F _hF _hchar P hdegree hP
  have hprofile : 0 ≤ profile D N := (sq_nonneg (D : ℝ)).trans (degree_square_le_profile D N hN)
  by_cases hline : D = 1
  · have hb := LinearPlaneGridBound.linear_grid_card P hP (hdegree.trans hline) N
    have hc : ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ 3 * (N : ℝ) := by
      exact_mod_cast hb.trans (show 2 * N + 1 ≤ 3 * N by omega)
    have hL : (1 : ℝ) ≤ (logarithmicBudget N : ℝ) ^ 17 := by
      apply one_le_pow₀
      exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
    have hbase : (N : ℝ) ≤ profile D N := by
      rw [hline]
      simpa only [profile, Nat.cast_one, one_pow, one_div_one, Real.rpow_one, one_mul] using
        le_mul_of_one_le_left (Nat.cast_nonneg N) hL
    have hm := mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith only [hc, hm, mul_nonneg hC₀.le hprofile]
  · have hD2 : 2 ≤ D := by omega
    have hb := hcount D N hD2 hN F P hdegree hP
    nlinarith only [hb, hprofile]

theorem finite_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 0 < D → 1 ≤ N →
    ∀ (F : Type*) [Field F] [CharZero F], ∀ P : Polynomial (Polynomial F),
    PlaneCurvePointCount.degree P = D → Irreducible P → ∀ S : Finset (ℤ × ℤ),
    (∀ z ∈ S, P.evalEval (z.1 : F) (z.2 : F) = 0 ∧ z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N) →
    (S.card : ℝ) ≤ C * profile D N := by
  obtain ⟨C, hC, hcount⟩ := grid_count
  refine ⟨C, hC, ?_⟩
  intro D N hD hN F _hF _hchar P hdegree hP S hS
  have hsub : S ⊆ PlaneCurvePointCount.grid P N := by
    intro z hz
    obtain ⟨hzero, hx, hy⟩ := hS z hz
    apply (PlaneCurvePointCount.mem_grid P N z).mpr
    refine ⟨?_, ?_, hzero⟩
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hx
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hy
  have hc : (S.card : ℝ) ≤ ((PlaneCurvePointCount.grid P N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (hcount D N hD hN F P hdegree hP)

def constant : ℝ := Classical.choose grid_count.{u}

theorem constant_pos : 0 < constant.{u} := (Classical.choose_spec grid_count.{u}).1

theorem grid_le (D N : ℕ) (hD : 0 < D) (hN : 1 ≤ N)
    (F : Type u) [Field F] [CharZero F] (P : Polynomial (Polynomial F))
    (hdegree : PlaneCurvePointCount.degree P = D) (hP : Irreducible P) :
    ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ constant.{u} * profile D N :=
  (Classical.choose_spec grid_count.{u}).2 D N hD hN F P hdegree hP

end PaperP1.QuadraticAllDegreePlaneCount
