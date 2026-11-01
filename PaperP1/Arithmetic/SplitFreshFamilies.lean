module

public import PaperP1.Arithmetic.SplitKernelStates

/-! # Actual fresh factor families at fixed centre and prescribed divisor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitFreshFamilies

open Finset PaperP1.EvenPrimePatterns PaperP1.SplitOffsetProducts PaperP1.SplitKernelStates
open PaperP1.PrescribedPatternDivisors PaperP1.ExposureAssignmentBudget

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def family (A : Finset ℤ) (rank : ι → ℕ) (i : ι) (T : Finset (ι → ℕ)) :
    Finset (freshPatterns rank i → ℕ) := T.image fun n ↦ (stepRecord A rank i n).2

theorem family_product (A : Finset ℤ) (rank : ι → ℕ) (i : ι) (T : Finset (ι → ℕ)) (z e : ℕ)
    (hT : ∀ n ∈ T, n i = z ∧ prescribed (kernels A n) rank i = e ∧ IsSquare (∏ j, kernels A n j)) :
    ∀ D ∈ family A rank i T, ∏ S, D S = kernel A z / e := by
  intro D hD
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hD
  obtain ⟨hnz, hne, hsq⟩ := hT n hn
  have hp := fresh_product A rank i n hsq
  rw [hne] at hp
  simpa only [kernels, hnz] using hp

theorem family_squarefree (A : Finset ℤ) (rank : ι → ℕ) (i : ι) (T : Finset (ι → ℕ)) :
    ∀ D ∈ family A rank i T, ∀ S, Squarefree (D S) := by
  intro D hD S
  obtain ⟨n, _, rfl⟩ := mem_image.mp hD
  exact part_squarefree (kernels A n) S.val

theorem family_coprime (A : Finset ℤ) (rank : ι → ℕ) (i : ι) (T : Finset (ι → ℕ)) :
    ∀ D ∈ family A rank i T, Pairwise fun S R ↦ Nat.Coprime (D S) (D R) := by
  intro D hD
  obtain ⟨n, _, rfl⟩ := mem_image.mp hD
  exact fresh_coprime A rank i n

theorem family_card_le (A : Finset ℤ) (rank : ι → ℕ) (i : ι) (T : Finset (ι → ℕ)) (z e : ℕ)
    (hT : ∀ n ∈ T, n i = z ∧ prescribed (kernels A n) rank i = e ∧ IsSquare (∏ j, kernels A n j)) :
    (family A rank i T).card ≤ (2 ^ (Fintype.card ι - 1)) ^ (kernel A z).primeFactors.card := by
  by_cases hnon : T.Nonempty
  · obtain ⟨n, hn⟩ := hnon
    obtain ⟨hnz, hne, hsq⟩ := hT n hn
    have hdiv := prescribed_dvd_coordinate (kernels A n) (kernels_squarefree A n) hsq rank i
    rw [hne] at hdiv
    have hediv : e ∣ kernel A z := by simpa only [kernels, hnz] using hdiv
    exact card_fresh_families rank i (kernel A z / e) (kernel A z) (kernel_pos A z)
      (Nat.div_dvd_of_dvd hediv) (family A rank i T)
      (family_squarefree A rank i T) (family_product A rank i T z e hT) (family_coprime A rank i T)
  · have hempty : T = ∅ := not_nonempty_iff_eq_empty.mp hnon
    simp only [hempty, family, image_empty, card_empty]
    exact Nat.zero_le _

end PaperP1.SplitFreshFamilies
