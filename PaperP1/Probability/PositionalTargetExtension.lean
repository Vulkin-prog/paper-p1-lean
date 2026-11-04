module

public import PaperP1.Probability.PositionalBernoulliProducts

/-! # Restoring the missing single-site Poisson arrivals on the original grid -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalTargetExtension

open Finset PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw PaperP1.PositionalCompoundPoisson
  PaperP1.PositionalBernoulliProducts

variable {ι : Type*}

local instance positionalTargetExtensionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem target_congr (G : Finset ι) (E : Finset (Finset ι)) (p p' : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x ∈ G, p x = p' x) : target G E p q = target G E p' q := by
  unfold target
  congr 1
  apply prod_congr rfl
  intro x hx
  rw [hp x hx]

theorem incidence_zero_outside (G : Finset ι) (E : Finset (Finset ι)) (q : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G) (x : ι) (hx : x ∉ G) : incidence E q x = 0 := by
  unfold incidence
  apply sum_eq_zero
  intro e he
  have hnot : x ∉ e := fun hxe ↦ hx (hE e he hxe)
  simp only [hnot, ite_false]

theorem factorization (G H : Finset ι) (hGH : G ⊆ H) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G) : target H E p q = target G E p q * poisson (H \ G) p := by
  classical
  have hout : (∏ x ∈ H \ G, PositionalPoissonJump.jump (direction x) (p x - incidence E q x)) =
      poisson (H \ G) p := by
    rw [poisson, NormedSpace.exp_sum]
    apply prod_congr rfl
    intro x hx
    rw [incidence_zero_outside G E q hE x (mem_sdiff.mp hx).2, sub_zero,
      PositionalPoissonJump.jump, delta, map_sub, map_one]
  unfold target
  rw [← prod_sdiff (f := fun x ↦ PositionalPoissonJump.jump (direction x) (p x - incidence E q x)) hGH, hout]
  ring

theorem poisson_extension_error (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x) :
    ‖poisson G p - 1‖ ≤ (2 * ∑ x ∈ G, p x) * Real.exp (2 * ∑ x ∈ G, p x) := by
  let S := ∑ x ∈ G, p x • ofFinite (delta x)
  have hS : ‖S‖ ≤ 2 * ∑ x ∈ G, p x := by
    calc
      _ ≤ ∑ x ∈ G, ‖p x • ofFinite (delta x)‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ G, 2 * p x := sum_le_sum fun x hx ↦ norm_parameter_le x (p x) (hp x hx)
      _ = _ := (mul_sum _ _ _).symm
  have hlocal := BanachExponentialRemainder.norm_exp_sub_one_le S
  apply hlocal.trans
  exact mul_le_mul hS (Real.exp_le_exp.mpr hS) (Real.exp_nonneg _)
    (mul_nonneg (by norm_num) (sum_nonneg hp))

theorem restoration_bound (G H : Finset ι) (hGH : G ⊆ H) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G) (hp : ∀ x ∈ G, 0 ≤ p x - incidence E q x)
    (hq : ∀ e ∈ E, 0 ≤ q e) (hout : ∀ x ∈ H \ G, 0 ≤ p x) :
    ‖target H E p q - target G E p q‖ ≤
      (2 * ∑ x ∈ H \ G, p x) * Real.exp (2 * ∑ x ∈ H \ G, p x) := by
  rw [factorization G H hGH E p q hE,
    show target G E p q * poisson (H \ G) p - target G E p q = target G E p q * (poisson (H \ G) p - 1) by ring]
  have hh := norm_mul_le (target G E p q) (poisson (H \ G) p - 1)
  rw [norm_target G E p q hp hq, one_mul] at hh
  exact hh.trans (poisson_extension_error (H \ G) p hout)

end PaperP1.PositionalTargetExtension
