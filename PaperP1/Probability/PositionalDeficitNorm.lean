module

public import PaperP1.Probability.PositionalFiniteLaw
public import PaperP1.Probability.RetainedDeficitNorm

/-! # Positional retained-reference errors cost the same two actual deficits -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalDeficitNorm

open Finset PaperP1.Affine PaperP1.PositionalFiniteLaw PaperP1.FiniteConvolutionAlgebra
  PaperP1.RetainedReferenceIdentity

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U)

def siteTerm (p : ι → ℝ) (x : ι) : FieldLaw ι := scalar (p x) * delta x

omit [DecidableEq ι] in
theorem family_term (p : ι → ℝ) (I : Finset ι) :
    familyTerm (siteTerm p) 1 I = scalar (∏ x ∈ I, p x) * difference I := by
  simp only [familyTerm, siteTerm, one_pow, mul_one, prod_mul_distrib, ← map_prod, difference]

omit [DecidableEq ι] in
theorem scalar_difference_norm (a : ℝ) (I : Finset ι) (ha : 0 ≤ a) :
    l1Norm (scalar a * difference I) ≤ (2 : ℝ) ^ I.card * a := by
  calc
    _ ≤ l1Norm (scalar a) * l1Norm (difference I) := l1Norm_mul _ _
    _ = a * l1Norm (difference I) := by rw [l1Norm_scalar, abs_of_nonneg ha]
    _ ≤ a * (2 : ℝ) ^ I.card := mul_le_mul_of_nonneg_left (difference_l1Norm I) ha
    _ = _ := mul_comm _ _

omit [DecidableEq ι] in
theorem scalar_two_differences_norm (a : ℝ) (I J : Finset ι) (ha : 0 ≤ a) :
    l1Norm (scalar a * (difference I * difference J)) ≤ (2 : ℝ) ^ (I.card + J.card) * a := by
  have hprod : l1Norm (difference I * difference J) ≤ (2 : ℝ) ^ (I.card + J.card) := by
    apply (l1Norm_mul _ _).trans
    rw [pow_add]
    exact mul_le_mul (difference_l1Norm I) (difference_l1Norm J) (l1Norm_nonneg _)
      (by positivity)
  calc
    _ ≤ l1Norm (scalar a) * l1Norm (difference I * difference J) := l1Norm_mul _ _
    _ = a * l1Norm (difference I * difference J) := by rw [l1Norm_scalar, abs_of_nonneg ha]
    _ ≤ a * (2 : ℝ) ^ (I.card + J.card) := mul_le_mul_of_nonneg_left hprod ha
    _ = _ := mul_comm _ _

omit [DecidableEq ι] in
theorem direct_norm_bound (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x) :
    l1Norm (directDeficit S G (siteTerm p) (1 : FieldLaw ι)) ≤
      RetainedDeficitNorm.directMass S G p := by
  classical
  unfold directDeficit RetainedDeficitNorm.directMass
  apply (l1Norm_sum _ _).trans
  apply sum_le_sum
  intro I hI
  have hIG := mem_powerset.mp (mem_filter.mp hI).1
  rw [family_term]
  exact scalar_difference_norm _ I (prod_nonneg fun x hx ↦ hp x (hIG hx))

theorem compressed_norm_bound (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hcard : ∀ e ∈ E, e.card = 2) (hp : ∀ x ∈ G, 0 ≤ p x) (hq : ∀ e ∈ E, 0 ≤ q e) :
    l1Norm (compressedDeficit S G E (siteTerm p) (fun e ↦ scalar (q e) * difference e) (1 : FieldLaw ι)) ≤
      RetainedDeficitNorm.compressedMass S G E p q := by
  classical
  unfold compressedDeficit RetainedDeficitNorm.compressedMass
  apply (l1Norm_sum _ _).trans
  apply sum_le_sum
  intro e he
  apply (l1Norm_sum _ _).trans
  apply sum_le_sum
  intro A hA
  have hAG := (mem_powerset.mp (mem_filter.mp hA).1).trans (sdiff_subset : G \ e ⊆ G)
  have hnonneg : 0 ≤ q e * ∏ x ∈ A, p x :=
    mul_nonneg (hq e he) (prod_nonneg fun x hx ↦ hp x (hAG hx))
  have hterm : (scalar (q e) * difference e) * 1 ^ 2 * familyTerm (siteTerm p) 1 A =
      scalar (q e * ∏ x ∈ A, p x) * (difference e * difference A) := by
    rw [family_term, map_mul]
    ring
  rw [hterm]
  have hh := scalar_two_differences_norm (q e * ∏ x ∈ A, p x) e A hnonneg
  rw [hcard e he, Nat.add_comm 2 A.card] at hh
  exact hh.trans_eq (by ring)

theorem combined_norm_bound (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hcard : ∀ e ∈ E, e.card = 2) (hp : ∀ x ∈ G, 0 ≤ p x) (hq : ∀ e ∈ E, 0 ≤ q e) :
    l1Norm (directDeficit S G (siteTerm p) (1 : FieldLaw ι) +
      compressedDeficit S G E (siteTerm p) (fun e ↦ scalar (q e) * difference e) 1) ≤
      RetainedDeficitNorm.directMass S G p + RetainedDeficitNorm.compressedMass S G E p q :=
  (l1Norm_add _ _).trans (add_le_add (direct_norm_bound S G p hp)
    (compressed_norm_bound S G E p q hcard hp hq))

end PaperP1.PositionalDeficitNorm
