module

public import PaperP1.Arithmetic.LogarithmicQuadraticPlaneParameters
public import PaperP1.Arithmetic.CubicDegreeUniformFieldCount

/-! # A quadratic-degree real plane estimate over the entire degree range -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticDegreeUniformRealCount

open Polynomial Finset DegreeUniformAffineParameters

theorem uniform_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → 1 ≤ N →
    ∀ P : ℝ[X][X], PlaneCurvePointCount.degree P = D → Irreducible P →
    ∀ S : Finset (ℤ × ℤ),
    (∀ z ∈ S, P.evalEval (z.1 : ℝ) (z.2 : ℝ) = 0 ∧ z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N) →
    (S.card : ℝ) ≤ C * (D : ℝ) ^ 2 * (logarithmicBudget N : ℝ) ^ 17 *
      (N : ℝ) ^ (1 / (D : ℝ)) := by
  classical
  obtain ⟨C₀, hC₀, hcount⟩ := CubicDegreeUniformFieldCount.finite_field_count
  let A : ℝ := 300000 * Real.exp 4 * (3 : ℝ) ^ 17
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨2 * C₀ + A, by positivity, ?_⟩
  intro D N hD hN P hdegree hP S hS
  let L : ℝ := logarithmicBudget N
  let ρ : ℝ := (N : ℝ) ^ (1 / (D : ℝ))
  have hL : 1 ≤ L := by dsimp [L]; exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
  have hρ : 1 ≤ ρ := Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hT : 0 ≤ (D : ℝ) ^ 2 * L ^ 17 * ρ := by positivity
  by_cases hlow : D ≤ logarithmicBudget (2 * N)
  · have hDL : (D : ℝ) ≤ 2 * L := by
      have hn := LogarithmicQuadraticPlaneParameters.doubling N (by omega)
      have hcast : (D : ℝ) ≤ L + 1 := by
        dsimp [L]
        exact_mod_cast (show D ≤ logarithmicBudget N + 1 by omega)
      linarith only [hcast, hL]
    have hpow : L ^ 3 ≤ L ^ 17 := pow_le_pow_right₀ hL (by decide)
    have hb := hcount D N hD hN ℝ P hdegree hP S hS
    change (S.card : ℝ) ≤ C₀ * ((D : ℝ) ^ 3 * L ^ 2 * ρ) at hb
    have hm := mul_le_mul_of_nonneg_left hDL
      (show 0 ≤ C₀ * (D : ℝ) ^ 2 * L ^ 2 * ρ by positivity)
    have hsmall : (S.card : ℝ) ≤ 2 * C₀ * (D : ℝ) ^ 2 * L ^ 17 * ρ := by
      calc
        _ ≤ C₀ * ((D : ℝ) ^ 3 * L ^ 2 * ρ) := hb
        _ = (C₀ * (D : ℝ) ^ 2 * L ^ 2 * ρ) * D := by ring
        _ ≤ (C₀ * (D : ℝ) ^ 2 * L ^ 2 * ρ) * (2 * L) := hm
        _ = 2 * C₀ * (D : ℝ) ^ 2 * L ^ 3 * ρ := by ring
        _ ≤ _ := by gcongr
    have hnonneg : 0 ≤ A * ((D : ℝ) ^ 2 * L ^ 17 * ρ) := mul_nonneg hA.le hT
    change (S.card : ℝ) ≤ (2 * C₀ + A) * (D : ℝ) ^ 2 * L ^ 17 * ρ
    nlinarith only [hsmall, hnonneg]
  · let q := (BivariateTotalDegreeChart.chart ℝ).symm P
    have hq : Irreducible q :=
      (MulEquiv.irreducible_iff (BivariateTotalDegreeChart.chart ℝ).symm.toRingEquiv.toMulEquiv).mpr hP
    have hqdegree : q.totalDegree = D := by
      have hh := BivariateTotalDegreeChart.chart_degree q
      change PlaneCurvePointCount.degree ((BivariateTotalDegreeChart.chart ℝ)
        ((BivariateTotalDegreeChart.chart ℝ).symm P)) = q.totalDegree at hh
      rw [AlgEquiv.apply_symm_apply, hdegree] at hh
      exact hh.symm
    let v : ℤ × ℤ → Fin 2 → ℤ := fun z ↦ ![z.2, z.1]
    have hinj : Function.Injective v := by
      intro z w he
      exact Prod.ext (congrFun he 1) (congrFun he 0)
    let T := S.image v
    have hTcard : T.card = S.card := card_image_of_injective _ hinj
    have hzero : ∀ z ∈ T, MvPolynomial.eval (fun i ↦ (z i : ℝ)) q = 0 := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      have hv : (fun i ↦ (v w i : ℝ)) = Fin.cons (w.2 : ℝ) (fun _ : Fin 1 ↦ (w.1 : ℝ)) := by
        funext i
        fin_cases i <;> rfl
      rw [hv, ← BivariateTotalDegreeChart.chart_evaluation, AlgEquiv.apply_symm_apply]
      exact (hS w hw).1
    have hbox : ∀ z ∈ T, ∀ i, (z i).natAbs ≤ N := by
      intro z hz i
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      fin_cases i
      · exact (hS w hw).2.2
      · exact (hS w hw).2.1
    have hb := LogarithmicQuadraticPlaneParameters.high_degree_count q hq N (by omega)
      (by rw [hqdegree]; omega) T hzero hbox
    rw [hTcard, hqdegree] at hb
    have hbig : (S.card : ℝ) ≤ A * (D : ℝ) ^ 2 * L ^ 17 * ρ :=
      hb.trans (le_mul_of_one_le_right (by positivity) hρ)
    have hnonneg : 0 ≤ (2 * C₀) * ((D : ℝ) ^ 2 * L ^ 17 * ρ) := mul_nonneg (by positivity) hT
    change (S.card : ℝ) ≤ (2 * C₀ + A) * (D : ℝ) ^ 2 * L ^ 17 * ρ
    nlinarith only [hbig, hnonneg]

theorem grid_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → 1 ≤ N →
    ∀ P : ℝ[X][X], PlaneCurvePointCount.degree P = D → Irreducible P →
    ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ C * (D : ℝ) ^ 2 *
      (logarithmicBudget N : ℝ) ^ 17 * (N : ℝ) ^ (1 / (D : ℝ)) := by
  obtain ⟨C, hC, hcount⟩ := uniform_count
  refine ⟨C, hC, ?_⟩
  intro D N hD hN P hdegree hP
  apply hcount D N hD hN P hdegree hP (PlaneCurvePointCount.grid P N)
  intro z hz
  obtain ⟨hx, hy, hzero⟩ := (PlaneCurvePointCount.mem_grid P N z).mp hz
  refine ⟨hzero, ?_, ?_⟩
  · have hh : (z.1.natAbs : ℤ) ≤ (N : ℤ) := by simpa only [Int.natCast_natAbs] using hx
    exact_mod_cast hh
  · have hh : (z.2.natAbs : ℤ) ≤ (N : ℤ) := by simpa only [Int.natCast_natAbs] using hy
    exact_mod_cast hh

end PaperP1.QuadraticDegreeUniformRealCount
