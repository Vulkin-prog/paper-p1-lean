module

public import PaperP1.Probability.PositionalPoissonPairs
public import PaperP1.Probability.PositionalPairDeletion

/-! # Actual accidental-edge probabilities in an independent Poisson field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalPoissonAccidents

open Finset PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalPairDeletion PaperP1.PositionalPoissonObservables

variable {ι : Type*}

local instance poissonAccidentsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem edge_bound (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x)
    (e : Finset ι) (he : e ⊆ G) (hcard : e.card = 2) :
    Summable (fun v : Configuration ι ↦ coeff v (PositionalBernoulliProducts.poisson G p) *
      (if ∀ x ∈ e, 0 < v x then 1 else 0)) ∧
      (∑' v : Configuration ι, coeff v (PositionalBernoulliProducts.poisson G p) *
        (if ∀ x ∈ e, 0 < v x then 1 else 0)) ≤ ∏ x ∈ e, p x := by
  classical
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hcard
  have hx := he (mem_insert_self x {y})
  have hy := he (mem_insert_of_mem (mem_singleton_self y))
  have hpred (v : Configuration ι) : (∀ z ∈ ({x, y} : Finset ι), 0 < v z) ↔
      0 < v x ∧ 0 < v y := by simp
  simpa only [hpred, prod_pair hxy] using
    PositionalPoissonPairs.occupied_pair_bound G p hp x y hx hy hxy

theorem active_count_bound (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x)
    (E : Finset (Finset ι)) (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    Summable (fun v : Configuration ι ↦ coeff v (PositionalBernoulliProducts.poisson G p) *
      ((activeEdges E v).card : ℝ)) ∧
      (∑' v : Configuration ι, coeff v (PositionalBernoulliProducts.poisson G p) *
        ((activeEdges E v).card : ℝ)) ≤ ∑ e ∈ E, ∏ x ∈ e, p x := by
  have hseries := hasSum_sum (s := E) (fun e he ↦ (edge_bound G p hp e
    (hE e he).1 (hE e he).2).1.hasSum)
  have heq (v : Configuration ι) :
      (∑ e ∈ E, coeff v (PositionalBernoulliProducts.poisson G p) *
        (if ∀ x ∈ e, 0 < v x then 1 else 0)) =
        coeff v (PositionalBernoulliProducts.poisson G p) * ((activeEdges E v).card : ℝ) := by
    rw [← mul_sum]
    congr 1
    exact sum_boole (fun e ↦ ∀ x ∈ e, 0 < v x) E
  simp_rw [heq] at hseries
  refine ⟨hseries.summable, hseries.tsum_eq.trans_le ?_⟩
  exact sum_le_sum (fun e he ↦ (edge_bound G p hp e (hE e he).1 (hE e he).2).2)

theorem any_active_bound (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x)
    (E : Finset (Finset ι)) (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    Summable (fun v : Configuration ι ↦ if (activeEdges E v).Nonempty then
      coeff v (PositionalBernoulliProducts.poisson G p) else 0) ∧
      (∑' v : Configuration ι, if (activeEdges E v).Nonempty then
        coeff v (PositionalBernoulliProducts.poisson G p) else 0) ≤ ∑ e ∈ E, ∏ x ∈ e, p x := by
  have hm := active_count_bound G p hp E hE
  have hnonneg := (poisson_isProbability G p hp).1
  have hpoint (v : Configuration ι) :
      (if (activeEdges E v).Nonempty then coeff v (PositionalBernoulliProducts.poisson G p) else 0) ≤
        coeff v (PositionalBernoulliProducts.poisson G p) * ((activeEdges E v).card : ℝ) := by
    by_cases hv : (activeEdges E v).Nonempty
    · rw [ite_eq_left hv]
      have hc : (1 : ℝ) ≤ (activeEdges E v).card := by
        exact_mod_cast (card_pos.mpr hv : 0 < (activeEdges E v).card)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (hnonneg v)
    · rw [ite_eq_right hv]
      exact mul_nonneg (hnonneg v) (Nat.cast_nonneg _)
  have hs := Summable.of_nonneg_of_le
    (fun v ↦ by split_ifs; exact hnonneg v; exact le_rfl) hpoint hm.1
  exact ⟨hs, (hs.tsum_le_tsum hpoint hm.1).trans hm.2⟩

end PaperP1.PositionalPoissonAccidents
