module

public import PaperP1.Probability.PositivePositionalConvolution

/-! # The positive unsigned single-site and arithmetic-pair Poisson field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalCompoundPoisson

open Finset PaperP1.FiniteConvolutionAlgebra PaperP1.PositionalFiniteLaw
  PaperP1.CompletedPositionalLaw PaperP1.PositionalTotalMass PaperP1.PositionalPoissonJump
  PaperP1.PositivePositionalConvolution

variable {ι : Type*}

local instance positionalCompoundDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def incidence (E : Finset (Finset ι)) (q : Finset ι → ℝ) (x : ι) : ℝ :=
  ∑ e ∈ E, if x ∈ e then q e else 0

def target (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ) : Space ι :=
  (∏ x ∈ G, jump (direction x) (p x - incidence E q x)) *
    ∏ e ∈ E, jump (∑ x ∈ e, direction x) (q e)

theorem target_isProbability (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x ∈ G, 0 ≤ p x - incidence E q x) (hq : ∀ e ∈ E, 0 ≤ q e) :
    IsProbability (target G E p q) :=
  mul_isProbability (prod_isProbability G _ (fun x hx ↦ jump_isProbability _ _ (hp x hx)))
    (prod_isProbability E _ (fun e he ↦ jump_isProbability _ _ (hq e he)))

theorem norm_target (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x ∈ G, 0 ≤ p x - incidence E q x) (hq : ∀ e ∈ E, 0 ≤ q e) :
    ‖target G E p q‖ = 1 := norm_isProbability (target_isProbability G E p q hp hq)

theorem pair_generator (e : Finset ι) (he : e.card = 2) :
    ofFinite (atom (∑ x ∈ e, direction x)) - 1 =
      (∑ x ∈ e, ofFinite (delta x)) + ofFinite (difference e) := by
  classical
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp he
  rw [sum_pair hxy, ← atom_mul, map_mul]
  simp only [sum_pair hxy, difference, prod_pair hxy, map_mul, delta, map_sub, map_one]
  ring

theorem incidence_sum (G : Finset ι) (E : Finset (Finset ι)) (q : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G) :
    (∑ x ∈ G, incidence E q x • ofFinite (delta x)) =
      ∑ e ∈ E, q e • ∑ x ∈ e, ofFinite (delta x) := by
  classical
  unfold incidence
  simp_rw [sum_smul, ite_smul, zero_smul]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  rw [smul_sum]
  have hfilter : G.filter (fun x ↦ x ∈ e) = e := by
    ext x
    simp only [mem_filter]
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨hE e he hx, hx⟩⟩
  simpa only [hfilter] using (sum_filter (s := G) (p := fun x ↦ x ∈ e)
    (f := fun x ↦ q e • ofFinite (delta x))).symm

theorem target_exponential (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    target G E p q = NormedSpace.exp
      ((∑ x ∈ G, p x • ofFinite (delta x)) + ∑ e ∈ E, q e • ofFinite (difference e)) := by
  classical
  have hsite (x : ι) : jump (direction x) (p x - incidence E q x) =
      NormedSpace.exp ((p x - incidence E q x) • ofFinite (delta x)) := by
    rw [jump, delta, map_sub, map_one]
  have hedge (e : Finset ι) (he : e ∈ E) : jump (∑ x ∈ e, direction x) (q e) =
      NormedSpace.exp (q e • ((∑ x ∈ e, ofFinite (delta x)) + ofFinite (difference e))) := by
    rw [jump, pair_generator e (hE e he).2]
  rw [target]
  simp_rw [hsite]
  have hprod : (∏ e ∈ E, jump (∑ x ∈ e, direction x) (q e)) =
      ∏ e ∈ E, NormedSpace.exp (q e • ((∑ x ∈ e, ofFinite (delta x)) + ofFinite (difference e))) :=
    prod_congr rfl hedge
  rw [hprod, ← NormedSpace.exp_sum, ← NormedSpace.exp_sum, ← NormedSpace.exp_add]
  congr 1
  simp_rw [sub_smul, smul_add]
  rw [sum_sub_distrib, sum_add_distrib, ← incidence_sum G E q (fun e he ↦ (hE e he).1)]
  abel

end PaperP1.PositionalCompoundPoisson
