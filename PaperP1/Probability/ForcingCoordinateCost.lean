module

public import PaperP1.Probability.FiniteCoupling
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # The positive coordinate cost of a specified Palm forcing

The cost is the sum of absolute coordinate differences after deleting the
forced source. It retains the diagonal square of each heterogeneous marginal.
The directed-footprint bound is a finite inequality; it asserts no rate and
does not identify the cost with a distance between laws.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ForcingCoordinateCost

open Finset PaperP1.Algebra PaperP1.Probability

local instance forcingCoordinateCostDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]

def coordinateCost (G : Finset ι) (J : ι → Ω → Bool) (F : ι → Ω → Ω)
    (a : ι) (ω : Ω) : ℝ :=
  ∑ b ∈ G, |indicatorValue (J b ω) -
    (indicatorValue (J b (F a ω)) - if b = a then (1 : ℝ) else 0)|

def offsiteCost (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool)
    (F : ι → Ω → Ω) (a : ι) : ℝ :=
  finiteExpectation P.weight (fun ω ↦
    ∑ b ∈ G.erase a, |(indicatorValue (J b ω) : ℝ) - indicatorValue (J b (F a ω))|)

def cost (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool)
    (F : ι → Ω → Ω) : ℝ :=
  ∑ a ∈ G, exactMarginal P J a * finiteExpectation P.weight (coordinateCost G J F a)

def joint (P : FiniteProbability Ω) (J : ι → Ω → Bool) (a b : ι) : ℝ :=
  finiteExpectation P.weight (fun ω ↦ indicatorValue (J a ω) * indicatorValue (J b ω))

omit [Fintype Ω] in
theorem pointwise_deletion {G : Finset ι} {a : ι} (ha : a ∈ G)
    (J : ι → Ω → Bool) (F : ι → Ω → Ω) (hF : ∀ ω, J a (F a ω) = true) (ω : Ω) :
    coordinateCost G J F a ω =
      (∑ b ∈ G.erase a, |(indicatorValue (J b ω) : ℝ) - indicatorValue (J b (F a ω))|) +
        indicatorValue (J a ω) := by
  unfold coordinateCost
  rw [← sum_erase_add G (fun b ↦ |(indicatorValue (J b ω) : ℝ) -
    (indicatorValue (J b (F a ω)) - if b = a then 1 else 0)|) ha]
  congr 1
  · apply sum_congr rfl
    intro b hb
    have hba := (mem_erase.mp hb).1
    simp only [hba, ite_false, sub_zero]
  · rw [hF]
    cases J a ω <;> norm_num [indicatorValue]

theorem exact_diagonal_decomposition (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (F : ι → Ω → Ω)
    (hF : ∀ a ∈ G, ∀ ω, J a (F a ω) = true) :
    cost G P J F = (∑ a ∈ G, (exactMarginal P J a) ^ 2) +
      ∑ a ∈ G, exactMarginal P J a * offsiteCost G P J F a := by
  unfold cost
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  have he : coordinateCost G J F a = fun ω ↦
      (∑ b ∈ G.erase a, |(indicatorValue (J b ω) : ℝ) - indicatorValue (J b (F a ω))|) +
        indicatorValue (J a ω) := funext (pointwise_deletion ha J F (hF a ha))
  rw [he]
  rw [finiteExpectation_add]
  change exactMarginal P J a * (offsiteCost G P J F a + exactMarginal P J a) = _
  ring

theorem offsiteCost_nonneg (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (F : ι → Ω → Ω) (a : ι) :
    0 ≤ offsiteCost G P J F a :=
  finiteExpectation_nonneg P (fun _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _)

theorem diagonal_lower (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (F : ι → Ω → Ω)
    (hF : ∀ a ∈ G, ∀ ω, J a (F a ω) = true) :
    (∑ a ∈ G, (exactMarginal P J a) ^ 2) ≤ cost G P J F := by
  rw [exact_diagonal_decomposition G P J F hF]
  exact le_add_of_nonneg_right (sum_nonneg fun a _ ↦
    mul_nonneg (exactMarginal_nonneg P J a) (offsiteCost_nonneg G P J F a))

omit [DecidableEq ι] in
/-- The weighted Palm identity is used only for one target indicator here.
The actual private-prime construction proves it for every full observable. -/
theorem coordinate_upper (P : FiniteProbability Ω) (J : ι → Ω → Bool)
    (F : ι → Ω → Ω) (a b : ι)
    (hPalm : exactMarginal P J a *
      finiteExpectation P.weight (fun ω ↦ indicatorValue (J b (F a ω))) = joint P J a b) :
    exactMarginal P J a * finiteExpectation P.weight
      (fun ω ↦ |(indicatorValue (J b ω) : ℝ) - indicatorValue (J b (F a ω))|) ≤
        exactMarginal P J a * exactMarginal P J b + joint P J a b := by
  have hp := exactMarginal_nonneg P J a
  have hpoint (ω : Ω) : |(indicatorValue (J b ω) : ℝ) - indicatorValue (J b (F a ω))| ≤
      indicatorValue (J b ω) + indicatorValue (J b (F a ω)) := by
    cases J b ω <;> cases J b (F a ω) <;> norm_num [indicatorValue]
  have h := mul_le_mul_of_nonneg_left (finiteExpectation_mono P hpoint) hp
  rw [finiteExpectation_add, mul_add, hPalm] at h
  exact h

theorem offsite_footprint_upper (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (F : ι → Ω → Ω) (a : ι) (D : Finset ι)
    (hD : ∀ b ∈ G.erase a, b ∉ D → ∀ ω, J b (F a ω) = J b ω)
    (hPalm : ∀ b ∈ G.erase a, exactMarginal P J a *
      finiteExpectation P.weight (fun ω ↦ indicatorValue (J b (F a ω))) = joint P J a b) :
    exactMarginal P J a * offsiteCost G P J F a ≤
      ∑ b ∈ (G.erase a) ∩ D,
        (exactMarginal P J a * exactMarginal P J b + joint P J a b) := by
  unfold offsiteCost
  rw [finiteExpectation_sum, mul_sum]
  have he : (∑ b ∈ G.erase a, exactMarginal P J a * finiteExpectation P.weight
      (fun ω ↦ |(indicatorValue (J b ω) : ℝ) - indicatorValue (J b (F a ω))|)) =
      ∑ b ∈ (G.erase a) ∩ D, exactMarginal P J a * finiteExpectation P.weight
        (fun ω ↦ |(indicatorValue (J b ω) : ℝ) - indicatorValue (J b (F a ω))|) := by
    symm
    apply sum_subset (inter_subset_left)
    intro b hb hout
    have hn : b ∉ D := by
      intro h
      exact hout (mem_inter.mpr ⟨hb, h⟩)
    simp only [hD b hb hn, sub_self, abs_zero, finiteExpectation_const, mul_zero]
  rw [he]
  apply sum_le_sum
  intro b hb
  exact coordinate_upper P J F a b (hPalm b (mem_inter.mp hb).1)

theorem total_footprint_upper (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (F : ι → Ω → Ω) (D : ι → Finset ι)
    (hF : ∀ a ∈ G, ∀ ω, J a (F a ω) = true)
    (hD : ∀ a ∈ G, ∀ b ∈ G.erase a, b ∉ D a → ∀ ω, J b (F a ω) = J b ω)
    (hPalm : ∀ a ∈ G, ∀ b ∈ G.erase a, exactMarginal P J a *
      finiteExpectation P.weight (fun ω ↦ indicatorValue (J b (F a ω))) = joint P J a b) :
    cost G P J F ≤ (∑ a ∈ G, (exactMarginal P J a) ^ 2) +
      ∑ a ∈ G, ∑ b ∈ (G.erase a) ∩ D a,
        (exactMarginal P J a * exactMarginal P J b + joint P J a b) := by
  rw [exact_diagonal_decomposition G P J F hF]
  gcongr with a ha
  exact offsite_footprint_upper G P J F a (D a) (hD a ha) (hPalm a ha)

end PaperP1.ForcingCoordinateCost
