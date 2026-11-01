module

public import PaperP1.Combinatorics.GraphStarWeights

/-! # A stronger star bound and the original marked-isolate generating function -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MarkedGraphGenerator

open Finset PaperP1.GraphStarWeights

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def total (marks : Finset V) (z : ℝ) : ℝ := ∑ D ∈ families G marks, z ^ D.card

theorem degree_profile_bound (marks : Finset V) (z : ℝ) (hz : 0 ≤ z) :
    total G marks z ≤ Real.exp ((marks.card : ℝ) * z +
      ∑ c, z * ((1 + z) ^ G.degree c - 1)) := by
  have h := heterogeneous_generating_bound G marks (fun _ : V ↦ z) (fun _ ↦ hz)
  simpa only [PaperP1.FinitePolymerBound.generating, PaperP1.FinitePolymerBound.weight,
    prod_const, sum_const, nsmul_eq_mul, G.card_neighborFinset_eq_degree, total] using h

theorem polynomial_star_bound (marks : Finset V) (z : ℝ) (hz : 0 ≤ z) :
    total G marks z ≤ Real.exp ((marks.card : ℝ) * z +
      (Fintype.card V : ℝ) * z * ((1 + z) ^ G.maxDegree - 1)) := by
  have hdegrees : (∑ c : V, z * ((1 + z) ^ G.degree c - 1)) ≤
      (Fintype.card V : ℝ) * z * ((1 + z) ^ G.maxDegree - 1) := by
    calc
      _ ≤ ∑ _c : V, z * ((1 + z) ^ G.maxDegree - 1) := by
        apply sum_le_sum
        intro c _
        apply mul_le_mul_of_nonneg_left _ hz
        apply sub_le_sub_right
        exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + z) (G.degree_le_maxDegree c)
      _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring
  exact (degree_profile_bound G marks z hz).trans (Real.exp_le_exp.mpr (add_le_add (le_refl _) hdegrees))

/-- This estimate holds for every z>=0, without a small-activity condition. -/
theorem exponential_star_bound (marks : Finset V) (z : ℝ) (hz : 0 ≤ z) :
    total G marks z ≤ Real.exp ((marks.card : ℝ) * z +
      (Fintype.card V : ℝ) * z * (Real.exp ((G.maxDegree : ℝ) * z) - 1)) := by
  have hpower : (1 + z) ^ G.maxDegree ≤ Real.exp ((G.maxDegree : ℝ) * z) := by
    calc
      _ ≤ (Real.exp z) ^ G.maxDegree := pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp z]) _
      _ = _ := by rw [← Real.exp_nat_mul]
  apply (polynomial_star_bound G marks z hz).trans
  apply Real.exp_le_exp.mpr
  apply add_le_add (le_refl _)
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hpower 1) (by positivity)

theorem exponential_error_le_rational (x : ℝ) (hx : 0 ≤ x) (hsmall : 4 * x < 1) :
    Real.exp x - 1 ≤ 4 * x / (1 - 4 * x) := by
  have htwo : 0 < 2 - x := by linarith
  have hdenom : 0 < 1 - 4 * x := by linarith
  calc
    _ ≤ (2 + x) / (2 - x) - 1 := sub_le_sub_right (Real.exp_le_two_add_div_two_sub hx (by linarith)) 1
    _ = 2 * x / (2 - x) := by field_simp; ring
    _ ≤ _ := (div_le_div_iff₀ htwo hdenom).mpr (by nlinarith [sq_nonneg x])

theorem rational_star_bound (marks : Finset V) (z : ℝ) (hz : 0 ≤ z)
    (hsmall : (G.maxDegree : ℝ) * z < 2) :
    total G marks z ≤ Real.exp ((marks.card : ℝ) * z +
      2 * (Fintype.card V : ℝ) * (G.maxDegree : ℝ) * z ^ 2 /
        (2 - (G.maxDegree : ℝ) * z)) := by
  have hx : 0 ≤ (G.maxDegree : ℝ) * z := by positivity
  have he := sub_le_sub_right (Real.exp_le_two_add_div_two_sub hx hsmall) 1
  have hid : (2 + (G.maxDegree : ℝ) * z) / (2 - (G.maxDegree : ℝ) * z) - 1 =
      2 * ((G.maxDegree : ℝ) * z) / (2 - (G.maxDegree : ℝ) * z) := by
    have hden : 2 - (G.maxDegree : ℝ) * z ≠ 0 := by linarith
    field_simp
    ring
  rw [hid] at he
  have hbound := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ (Fintype.card V : ℝ) * z)
  have hid' : (Fintype.card V : ℝ) * z * (2 * ((G.maxDegree : ℝ) * z) /
      (2 - (G.maxDegree : ℝ) * z)) =
      2 * (Fintype.card V : ℝ) * (G.maxDegree : ℝ) * z ^ 2 /
        (2 - (G.maxDegree : ℝ) * z) := by ring
  rw [hid'] at hbound
  exact (exponential_star_bound G marks z hz).trans
    (Real.exp_le_exp.mpr (add_le_add (le_refl _) hbound))

/-- Article Lemma 7.4, with the exact admissible family and actual maximum degree. -/
theorem main_7_4 (marks : Finset V) (z : ℝ) (hz : 0 ≤ z)
    (hsmall : 4 * (G.maxDegree : ℝ) * z < 1) :
    total G marks z ≤ Real.exp ((marks.card : ℝ) * z +
      4 * (Fintype.card V : ℝ) * (G.maxDegree : ℝ) * z ^ 2 /
        (1 - 4 * (G.maxDegree : ℝ) * z)) := by
  have hx : 0 ≤ (G.maxDegree : ℝ) * z := by positivity
  have hsmall' : 4 * ((G.maxDegree : ℝ) * z) < 1 := by nlinarith
  have herror := exponential_error_le_rational ((G.maxDegree : ℝ) * z) hx hsmall'
  have hbound := mul_le_mul_of_nonneg_left herror (by positivity : (0 : ℝ) ≤ (Fintype.card V : ℝ) * z)
  have hidentity : (Fintype.card V : ℝ) * z * (4 * ((G.maxDegree : ℝ) * z) /
      (1 - 4 * ((G.maxDegree : ℝ) * z))) =
      4 * (Fintype.card V : ℝ) * (G.maxDegree : ℝ) * z ^ 2 /
        (1 - 4 * (G.maxDegree : ℝ) * z) := by ring
  rw [hidentity] at hbound
  exact (exponential_star_bound G marks z hz).trans
    (Real.exp_le_exp.mpr (add_le_add (le_refl _) hbound))

end PaperP1.MarkedGraphGenerator
