module

public import PaperP1.Model.InfiniteReplicaPositiveSum
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # The zero-length tuple case of positive replica moments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EmptyReplicaMoment

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteRademacher
  PaperP1.InfiniteReplicaPositiveSum PaperP1.InfiniteReplicaFormula
  PaperP1.Probability.CylinderExpectations

local instance emptyReplicaMomentMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance emptyReplicaMomentDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem block_eq_one {κ : Type*} (Y L : ℕ) (x : Fin 0 → ℕ) (color : Fin 0 → κ)
    (b : Fin 0 → Fin L → F₂) (k : κ) : conditionalBlock Y L x color b k = fun _ ↦ 1 := by
  unfold conditionalBlock
  simp only [IsEmpty.forall_iff, ite_true]
  exact condExp_const (measurable_restrictToFinite Y).comap_le (1 : ℝ)

theorem sum_constant {κ : Type*} [Fintype κ] (Y L : ℕ) (color : Fin 0 → κ)
    (c : ℕ → Fin L → F₂) (A : Finset (Fin 0 → ℕ)) (w : (Fin 0 → ℕ) → ℝ) :
    randomSum Y L color c A w = fun _ ↦ ∑ x ∈ A, w x := by
  funext ω
  unfold randomSum
  simp_rw [block_eq_one]
  simp only [prod_const_one, mul_one]

theorem positive_moment (q : ℕ) (D A₀ ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Y L : ℕ, ∀ (κ : Type*) [Fintype κ],
      ∀ color : Fin 0 → κ, ∀ c : ℕ → Fin L → F₂,
      ∀ A : Finset (Fin 0 → ℕ), ∀ w : (Fin 0 → ℕ) → ℝ,
      (∀ x ∈ A, 0 ≤ w x) → (∀ x ∈ A, w x ≤ D * (Real.log N) ^ A₀) →
        (∫ ω, (randomSum Y L color c A w ω) ^ (q + 1) ∂infiniteRademacherMeasure) ≤
          (N : ℝ) ^ ε * ∫ ω, randomSum Y L color c A w ω ∂infiniteRademacherMeasure := by
  obtain ⟨NW, hNW⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow (D ^ q) (A₀ * q) ε hε
  refine ⟨max 1 NW, ?_⟩
  intro N hN Y L κ _ color c A w hw hbound
  rw [sum_constant]
  have hμ : infiniteRademacherMeasure.real Set.univ = 1 := by simp
  simp only [integral_const, hμ, smul_eq_mul, one_mul]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hW : 0 ≤ D * (Real.log N) ^ A₀ := mul_nonneg hD (Real.rpow_nonneg hlog _)
  have hsum0 : 0 ≤ ∑ x ∈ A, w x := sum_nonneg hw
  have hsum : (∑ x ∈ A, w x) ≤ D * (Real.log N) ^ A₀ := by
    calc
      _ ≤ ∑ _x ∈ A, D * (Real.log N) ^ A₀ := sum_le_sum hbound
      _ = (A.card : ℝ) * (D * (Real.log N) ^ A₀) := by simp
      _ ≤ 1 * (D * (Real.log N) ^ A₀) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_le_one_of_subsingleton A) hW
      _ = _ := one_mul _
  have hpower : (D * (Real.log N) ^ A₀) ^ q ≤ (N : ℝ) ^ ε := by
    have heq : ((Real.log N) ^ A₀) ^ q = (Real.log N) ^ (A₀ * (q : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlog]
    rw [mul_pow, heq]
    exact hNW N (by omega)
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ hsum0 hsum q).trans hpower) hsum0

end PaperP1.EmptyReplicaMoment
