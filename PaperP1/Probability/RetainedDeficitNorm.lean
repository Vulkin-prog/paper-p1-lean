module

public import PaperP1.Algebra.RetainedReferenceIdentity
public import PaperP1.Probability.L1Norm

/-! # Ordinary ℓ¹ control by the two exact heterogeneous independent deficits -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedDeficitNorm

open Finset PaperP1.Affine PaperP1.Probability PaperP1.RetainedReferenceIdentity

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]
variable (S : κ → Submodule 𝔽₂ U)

def directMass (G : Finset κ) (p : κ → ℝ) : ℝ := by
  classical
  exact ∑ I ∈ G.powerset.filter (fun I ↦ relativeNullityOn S I ≠ 0),
    (2 : ℝ) ^ I.card * ∏ x ∈ I, p x

def compressedMass (G : Finset κ) (E : Finset (Finset κ)) (p : κ → ℝ) (q : Finset κ → ℝ) : ℝ :=
  ∑ e ∈ E, ∑ A ∈ failedExtensions S G e, q e * (2 : ℝ) ^ (A.card + 2) * ∏ x ∈ A, p x

omit [DecidableEq κ] in
theorem familyTerm_scalar (p : κ → ℝ) (I : Finset κ) :
    familyTerm (fun x ↦ scalar (p x)) forwardDifference I =
      scalar (∏ x ∈ I, p x) * (forwardDifference : SignedLaw ℝ) ^ I.card := by
  unfold familyTerm
  rw [map_prod]

theorem scalar_power_norm_le (a : ℝ) (n : ℕ) (ha : 0 ≤ a) :
    l1Norm (scalar a * (forwardDifference : SignedLaw ℝ) ^ n) ≤ (2 : ℝ) ^ n * a := by
  calc
    _ ≤ l1Norm (scalar a) * l1Norm ((forwardDifference : SignedLaw ℝ) ^ n) := l1Norm_mul _ _
    _ = a * l1Norm ((forwardDifference : SignedLaw ℝ) ^ n) := by rw [l1Norm_scalar, abs_of_nonneg ha]
    _ ≤ a * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_left (l1Norm_forwardDifference_pow_le n) ha
    _ = _ := mul_comm _ _

omit [DecidableEq κ] in
theorem familyTerm_norm_le (p : κ → ℝ) (I : Finset κ) (hp : ∀ x ∈ I, 0 ≤ p x) :
    l1Norm (familyTerm (fun x ↦ scalar (p x)) forwardDifference I) ≤
      (2 : ℝ) ^ I.card * ∏ x ∈ I, p x := by
  rw [familyTerm_scalar]
  exact scalar_power_norm_le _ _ (prod_nonneg hp)

omit [DecidableEq κ] in
theorem compressed_term_eq (p : κ → ℝ) (q : Finset κ → ℝ) (e A : Finset κ) :
    scalar (q e) * (forwardDifference : SignedLaw ℝ) ^ 2 *
      familyTerm (fun x ↦ scalar (p x)) forwardDifference A =
        scalar (q e * ∏ x ∈ A, p x) * forwardDifference ^ (A.card + 2) := by
  rw [familyTerm_scalar, map_mul, pow_add]
  ring1

omit [DecidableEq κ] in
theorem directDeficit_norm_le (G : Finset κ) (p : κ → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x) :
    l1Norm (directDeficit S G (fun x ↦ scalar (p x)) forwardDifference) ≤ directMass S G p := by
  classical
  unfold directDeficit directMass
  apply (l1Norm_sum _ _).trans
  apply sum_le_sum
  intro I hI
  have hIG := mem_powerset.mp (mem_filter.mp hI).1
  exact familyTerm_norm_le p I (fun x hx ↦ hp x (hIG hx))

theorem compressedDeficit_norm_le (G : Finset κ) (E : Finset (Finset κ))
    (p : κ → ℝ) (q : Finset κ → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x) (hq : ∀ e ∈ E, 0 ≤ q e) :
    l1Norm (compressedDeficit S G E (fun x ↦ scalar (p x)) (fun I ↦ scalar (q I)) forwardDifference) ≤
      compressedMass S G E p q := by
  classical
  unfold compressedDeficit compressedMass
  apply (l1Norm_sum _ _).trans
  apply sum_le_sum
  intro e he
  apply (l1Norm_sum _ _).trans
  apply sum_le_sum
  intro A hA
  have hAG := (mem_powerset.mp (mem_filter.mp hA).1).trans (sdiff_subset : G \ e ⊆ G)
  have hpA : 0 ≤ ∏ x ∈ A, p x := prod_nonneg (fun x hx ↦ hp x (hAG hx))
  rw [compressed_term_eq]
  calc
    _ ≤ (2 : ℝ) ^ (A.card + 2) * (q e * ∏ x ∈ A, p x) :=
      scalar_power_norm_le _ _ (mul_nonneg (hq e he) hpA)
    _ = _ := by ring1

theorem combined_norm_le (G : Finset κ) (E : Finset (Finset κ))
    (p : κ → ℝ) (q : Finset κ → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x) (hq : ∀ e ∈ E, 0 ≤ q e) :
    l1Norm (directDeficit S G (fun x ↦ scalar (p x)) forwardDifference +
      compressedDeficit S G E (fun x ↦ scalar (p x)) (fun I ↦ scalar (q I)) forwardDifference) ≤
        directMass S G p + compressedMass S G E p q :=
  (l1Norm_add _ _).trans
    (add_le_add (directDeficit_norm_le S G p hp) (compressedDeficit_norm_le S G E p q hp hq))

end PaperP1.RetainedDeficitNorm
