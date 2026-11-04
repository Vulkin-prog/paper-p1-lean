module

public import PaperP1.Probability.PositionalScalarProjection
public import PaperP1.Probability.PositionalBernoulliProducts
public import PaperP1.Probability.PoissonFactorialMoments

/-! # Exact subset-count laws and factorial moments of the independent Poisson field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalPoissonObservables

open Finset PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalScalarProjection PaperP1.PositivePositionalConvolution

variable {ι : Type*}

local instance poissonObservablesDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def subsetCount (S : Finset ι) : Configuration ι →+ ℕ :=
  Finsupp.liftAddHom (fun x ↦ if x ∈ S then AddMonoidHom.id ℕ else 0)

@[simp] theorem subsetCount_direction (S : Finset ι) (x : ι) :
    subsetCount S (direction x) = if x ∈ S then 1 else 0 := by
  by_cases hx : x ∈ S <;> simp [subsetCount, direction, hx]

theorem subsetCount_eq_sum (S : Finset ι) (v : Configuration ι) :
    subsetCount S v = ∑ x ∈ S, v x := by
  classical
  rw [subsetCount, Finsupp.liftAddHom_apply]
  have he (x : ι) (n : ℕ) : (if x ∈ S then AddMonoidHom.id ℕ else 0) n =
      if x ∈ S then n else 0 := by split_ifs <;> rfl
  change (∑ x ∈ v.support, (if x ∈ S then AddMonoidHom.id ℕ else 0) (v x)) = _
  simp_rw [he]
  rw [← sum_filter]
  apply sum_subset (fun x hx ↦ (mem_filter.mp hx).2)
  intro x hxS hx
  exact Finsupp.notMem_support_iff.mp (fun hv ↦ hx (mem_filter.mpr ⟨hv, hxS⟩))

theorem poisson_product (G : Finset ι) (p : ι → ℝ) :
    PositionalBernoulliProducts.poisson G p =
      ∏ x ∈ G, PositionalPoissonJump.jump (direction x) (p x) := by
  have hterm (x : ι) : PositionalPoissonJump.jump (direction x) (p x) =
      NormedSpace.exp (p x • ofFinite (delta x)) := by
    rw [PositionalPoissonJump.jump, delta, map_sub, map_one]
  simp_rw [hterm]
  exact NormedSpace.exp_sum G _

theorem poisson_isProbability (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x) :
    IsProbability (PositionalBernoulliProducts.poisson G p) := by
  rw [poisson_product]
  exact prod_isProbability G _ (fun x hx ↦ jump_isProbability _ _ (hp x hx))

theorem subset_projection (G S : Finset ι) (hS : S ⊆ G) (p : ι → ℝ) :
    projection (subsetCount S) (PositionalBernoulliProducts.poisson G p) =
      CompletedPoisson.poisson (∑ x ∈ S, p x) := by
  classical
  have hterm (x : ι) : projection (subsetCount S) (ofFinite (delta x)) =
      if x ∈ S then CompletedPoisson.delta else 0 := by
    rw [projection_delta, subsetCount_direction]
    by_cases hx : x ∈ S
    · rw [ite_eq_left hx, ite_eq_left hx]
      rw [CompletedPoisson.delta, Probability.forwardDifference, map_sub, Probability.atom_zero, map_one]
    · rw [ite_eq_right hx, ite_eq_right hx, Probability.atom_zero, map_one, sub_self]
  have hfilter : G.filter (fun x ↦ x ∈ S) = S := by
    ext x
    simp only [mem_filter]
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨hS hx, hx⟩⟩
  rw [PositionalBernoulliProducts.poisson, projection_exp, map_sum, CompletedPoisson.poisson]
  simp_rw [map_smul, hterm, smul_ite, smul_zero]
  rw [← sum_filter, hfilter, ← sum_smul]

theorem hasSum_subset_factorial (G S : Finset ι) (hS : S ⊆ G) (p : ι → ℝ)
    (hp : ∀ x ∈ G, 0 ≤ p x) (r : ℕ) :
    HasSum (fun v : Configuration ι ↦ coeff v (PositionalBernoulliProducts.poisson G p) *
      ((subsetCount S v).descFactorial r : ℝ)) ((∑ x ∈ S, p x) ^ r) := by
  let U := PositionalBernoulliProducts.poisson G p
  have hμ : 0 ≤ ∑ x ∈ S, p x := sum_nonneg (fun x hx ↦ hp x (hS hx))
  have hscalar := PoissonFactorialMoments.hasSum_mass_factorial (∑ x ∈ S, p x) hμ r
  have hs : Summable (fun k : ℕ ↦ CompletedLaw.coeff k (projection (subsetCount S) U) *
      (k.descFactorial r : ℝ)) := by
    simpa only [U, subset_projection G S hS p, CompletedPoisson.coeff_poisson] using hscalar.summable
  have hnonneg := (poisson_isProbability G p hp).1
  have hfield := summable_test (subsetCount S) U hnonneg
    (fun k ↦ (k.descFactorial r : ℝ)) (fun k ↦ Nat.cast_nonneg _) hs
  have he := test_eq (subsetCount S) U hnonneg
    (fun k ↦ (k.descFactorial r : ℝ)) (fun k ↦ Nat.cast_nonneg _) hs
  have hh := hfield.hasSum
  rw [he] at hh
  simpa only [U, subset_projection G S hS p, CompletedPoisson.coeff_poisson, hscalar.tsum_eq] using hh

end PaperP1.PositionalPoissonObservables
