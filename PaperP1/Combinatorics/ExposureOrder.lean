module

public import PaperP1.Combinatorics.ExposureWeights

/-! # Exact summed exposure weights, retaining the last coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExposureOrder

open Finset PaperP1.ExposureWeights

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def newWeight (H : Finset (Finset ι)) (w : Finset ι → ℝ) (first : Finset ι → ι) (i : ι) : ℝ :=
  ∑ S ∈ H, if first S = i then w S else 0

def prescribedWeight (H : Finset (Finset ι)) (w : Finset ι → ℝ)
    (first : Finset ι → ι) (i : ι) : ℝ := degree H w i - newWeight H w first i

theorem total_newWeight (H : Finset (Finset ι)) (w : Finset ι → ℝ) (first : Finset ι → ι) :
    (∑ i, newWeight H w first i) = ∑ S ∈ H, w S := by
  unfold newWeight
  rw [sum_comm]
  simp

omit [Fintype ι] in
theorem newWeight_last_zero (H : Finset (Finset ι)) (w : Finset ι → ℝ)
    (first : Finset ι → ι) (last : ι) (hfirst : ∀ S ∈ H, first S ≠ last) :
    newWeight H w first last = 0 := by
  apply sum_eq_zero
  intro S hS
  simp only [hfirst S hS, ite_false]

theorem exposure_identity (H : Finset (Finset ι)) (w : Finset ι → ℝ)
    (first : Finset ι → ι) (last : ι) (hfirst : ∀ S ∈ H, first S ≠ last) :
    (∑ i ∈ univ.erase last, (degree H w i / 2 - prescribedWeight H w first i)) =
      correction H w last := by
  have heq := sum_erase_add (univ : Finset ι)
    (fun i ↦ degree H w i / 2 - prescribedWeight H w first i) (mem_univ last)
  have hsum : (∑ i, (degree H w i / 2 - prescribedWeight H w first i)) =
      (∑ S ∈ H, w S) - (∑ i, degree H w i) / 2 := by
    unfold prescribedWeight
    rw [sum_sub_distrib, sum_sub_distrib, sum_div, total_newWeight]
    simp only [div_eq_mul_inv, ← sum_mul]
    ring
  rw [hsum, prescribedWeight, newWeight_last_zero H w first last hfirst] at heq
  rw [correction_as_totals]
  linarith

omit [Fintype ι] in
theorem prescribedWeight_filter (H : Finset (Finset ι)) (w : Finset ι → ℝ)
    (first : Finset ι → ι) (hfirst : ∀ S ∈ H, first S ∈ S) (i : ι) :
    prescribedWeight H w first i =
      ∑ S ∈ H.filter (fun S ↦ i ∈ S ∧ first S ≠ i), w S := by
  unfold prescribedWeight degree newWeight
  rw [sum_filter, ← sum_sub_distrib, sum_filter]
  apply sum_congr rfl
  intro S hS
  by_cases heq : first S = i
  · have hi : i ∈ S := heq ▸ hfirst S hS
    simp [heq, hi]
  · by_cases hi : i ∈ S <;> simp [heq, hi]

end PaperP1.ExposureOrder
