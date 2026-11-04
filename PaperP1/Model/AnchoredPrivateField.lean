module

public import PaperP1.Model.UnsignedAnchoredRunForcing
public import PaperP1.Model.CleanPivotWordCost
public import PaperP1.Probability.WeightedPositiveForcingCostLower

/-! # An actual field of unsigned private forcings with arbitrary arithmetic anchors

The anchor function is fixed before the random prime signs. Its preserved
raw value need not be fair. Every site has the full conditional prime
cylinder law, and every clean independent raw pair has its exact cost.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredPrivateField

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.AnchoredPrivateValues PaperP1.UniformFubini PaperP1.Probability PaperP1.Algebra
  PaperP1.PrivatePivotTargetFlip PaperP1.CleanPivotTargets PaperP1.PositiveForcingCostLower

local instance anchoredPrivateFieldDecidable (P : Prop) : Decidable P := Classical.propDecidable P

structure Data (M Y K : ℕ) (G : Finset ℕ) (anchor : G → Fin (K + 1)) : Prop where
  window : ∀ j : G, PaperP1.AnchoredWindowForcing.Data M j.val (K + 1) Y (anchor j)

variable {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K + 1)}

def force (D : Data M Y K G anchor) (b : Fin (K + 1) → F₂) (j : G) (ω : SampleSpace M) :
    SampleSpace M := PaperP1.AnchoredWindowForcing.force (D.window j) b ω

def indicator (b : Fin (K + 1) → F₂) (j : G) (ω : SampleSpace M) : Bool :=
  decide (PaperP1.BinaryForcingFlip.orbit b
    (valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω))

def rate (K : ℕ) : ℝ := (2 ^ K : ℝ)⁻¹

theorem rate_pos (K : ℕ) : 0 < rate K := by unfold rate; positivity

theorem indicator_value (b : Fin (K + 1) → F₂) (j : G) (ω : SampleSpace M) :
    (indicatorValue (indicator b j ω) : ℝ) = if PaperP1.BinaryForcingFlip.orbit b
      (valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω) then 1 else 0 := by
  by_cases h : PaperP1.BinaryForcingFlip.orbit b
      (valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω)
  · have hb : indicator b j ω = true := decide_eq_true h
    rw [hb, ite_eq_left h]
    rfl
  · have hb : indicator b j ω = false := decide_eq_false h
    rw [hb, ite_eq_right h]
    rfl

theorem force_hits (D : Data M Y K G anchor) (b : Fin (K + 1) → F₂)
    (j : G) (ω : SampleSpace M) : indicator b j (force D b j ω) = true :=
  decide_eq_true (PaperP1.AnchoredWindowForcing.hits (D.window j) b ω)

theorem indicator_marginal (D : Data M Y K G anchor) (b : Fin (K + 1) → F₂) (j : G) :
    exactMarginal (cylinderProbability M) (indicator b) j = rate K := by
  have hm := PaperP1.AnchoredWindowForcing.event_probability (D.window j) b
  have he : average (fun ω : SampleSpace M ↦ (indicatorValue (indicator b j ω) : ℝ)) =
      average (fun ω : SampleSpace M ↦ if ∃ s : F₂,
        valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω = fun i ↦ b i + s then (1 : ℝ) else 0) := by
    apply UniformFubini.congr
    intro ω
    rw [indicator_value]
    by_cases hp : PaperP1.BinaryForcingFlip.orbit b
        (valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω)
    · have he : ∃ s : F₂,
          valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω = fun i ↦ b i + s := hp
      rw [ite_eq_left hp, ite_eq_left he]
    · have he : ¬∃ s : F₂,
          valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω = fun i ↦ b i + s := hp
      rw [ite_eq_right hp, ite_eq_right he]
  exact he.trans hm

theorem weighted_palm (D : Data M Y K G anchor) (b : Fin (K + 1) → F₂)
    (j : G) (f : SampleSpace M → ℝ) :
    exactMarginal (cylinderProbability M) (indicator b) j *
      finiteExpectation (cylinderProbability M).weight (fun ω ↦ f (force D b j ω)) =
      finiteExpectation (cylinderProbability M).weight
        (fun ω ↦ indicatorValue (indicator b j ω) * f ω) := by
  have h := PaperP1.AnchoredWindowForcing.full_conditional (D.window j) b f
  have he : average (fun ω : SampleSpace M ↦ if ∃ s : F₂,
      valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω = fun i ↦ b i + s then f ω else 0) =
      average (fun ω : SampleSpace M ↦ indicatorValue (indicator b j ω) * f ω) := by
    apply UniformFubini.congr
    intro ω
    rw [indicator_value]
    by_cases hp : ∃ s : F₂,
        valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω = fun i ↦ b i + s
    · have ho : PaperP1.BinaryForcingFlip.orbit b
          (valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω) := hp
      rw [ite_eq_left hp, ite_eq_left ho, one_mul]
    · have ho : ¬PaperP1.BinaryForcingFlip.orbit b
          (valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω) := hp
      rw [ite_eq_right hp, ite_eq_right ho, zero_mul]
  rw [he] at h
  rw [indicator_marginal D]
  have hr : (2 ^ (K + 1 - 1) : ℝ)⁻¹ ≠ 0 := by positivity
  have hx := (eq_div_iff hr).mp h
  simpa only [Nat.add_sub_cancel, rate, force, cylinderProbability, average, mul_comm] using hx

def cost (D : Data M Y K G anchor) (b : Fin (K + 1) → F₂) : ℝ :=
  PaperP1.ForcingCoordinateCost.cost univ (cylinderProbability M) (indicator b) (force D b)

def offsite (D : Data M Y K G anchor) (b : Fin (K + 1) → F₂) : ℝ :=
  PaperP1.PositiveForcingCostLower.offsite univ (cylinderProbability M) (indicator b) (force D b)

theorem total_marginal (D : Data M Y K G anchor) (b : Fin (K + 1) → F₂) :
    (∑ j : G, exactMarginal (cylinderProbability M) (indicator b) j) = G.card * rate K := by
  simp only [indicator_marginal D, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]

theorem cost_diagonal_decomposition (D : Data M Y K G anchor) (b : Fin (K + 1) → F₂) :
    cost D b = G.card * (rate K) ^ 2 + offsite D b := by
  have h := PaperP1.ForcingCoordinateCost.exact_diagonal_decomposition univ (cylinderProbability M)
    (indicator b) (force D b) (fun j _ ω ↦ force_hits D b j ω)
  simpa only [cost, offsite, PaperP1.PositiveForcingCostLower.offsite, indicator_marginal D,
    sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul] using h

theorem expected_change_clean (D : Data M Y K G anchor) (hK : 1 ≤ K)
    (b : Fin (K + 1) → F₂) (j k : G) (selected : Free (anchor j)) {A N : ℕ}
    (hclean : k.val ∈ targets A N
      (PaperP1.AnchoredWindowForcing.pivots (D.window j) selected).val.val (K + 1)
      (otherPrimes (PaperP1.AnchoredWindowForcing.pivots (D.window j)) selected))
    (hjoint : Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (K + 1) ↦ j.val + i.val) (fun i : Fin (K + 1) ↦ k.val + i.val))) :
    finiteExpectation (cylinderProbability M).weight (fun ω ↦
      |(indicatorValue (indicator b k ω) : ℝ) - indicatorValue (indicator b k (force D b j ω))|) =
      rate K := by
  have hw : K + 1 ≤ (PaperP1.AnchoredWindowForcing.pivots (D.window j) selected).val.val :=
    (D.window j).word_width.trans ((D.window j).good selected).le
  have hc := PaperP1.CleanPivotWordCost.anchored_actual_cost
    (fun i : Fin (K + 1) ↦ j.val + i.val) (anchor j)
    (fun i ↦ by have := (D.window j).boundary_pos; omega)
    (PaperP1.AnchoredWindowForcing.pivots (D.window j)) b selected b hK hw hclean hjoint
  simp_rw [indicator_value]
  exact hc

theorem clean_weight (D : Data M Y K G anchor) (hK : 1 ≤ K)
    (b : Fin (K + 1) → F₂) (j k : G) (selected : Free (anchor j)) {A N : ℕ}
    (hclean : k.val ∈ targets A N
      (PaperP1.AnchoredWindowForcing.pivots (D.window j) selected).val.val (K + 1)
      (otherPrimes (PaperP1.AnchoredWindowForcing.pivots (D.window j)) selected))
    (hjoint : Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (K + 1) ↦ j.val + i.val) (fun i : Fin (K + 1) ↦ k.val + i.val))) :
    weight (cylinderProbability M) (indicator b) (force D b) (j, k) = (rate K) ^ 2 := by
  unfold weight
  rw [indicator_marginal D, expected_change_clean D hK b j k selected hclean hjoint, pow_two]

theorem selected_pairs_offsite_lower (D : Data M Y K G anchor) (hK : 1 ≤ K)
    (b : Fin (K + 1) → F₂) (P : Finset (G × G)) (hP : P ⊆ directed univ) {A N : ℕ}
    (hclean : ∀ p ∈ P, ∃ selected : Free (anchor p.1),
      p.2.val ∈ targets A N
        (PaperP1.AnchoredWindowForcing.pivots (D.window p.1) selected).val.val (K + 1)
        (otherPrimes (PaperP1.AnchoredWindowForcing.pivots (D.window p.1)) selected))
    (hjoint : ∀ p ∈ P, Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (K + 1) ↦ p.1.val + i.val) (fun i : Fin (K + 1) ↦ p.2.val + i.val))) :
    (rate K) ^ 2 * P.card ≤ offsite D b := by
  apply PaperP1.PositiveForcingCostLower.selected_pairs_lower univ
    (cylinderProbability M) (indicator b) (force D b) P hP
  intro p hp
  obtain ⟨i, hi⟩ := hclean p hp
  exact (clean_weight D hK b p.1 p.2 i hi (hjoint p hp)).ge

theorem selected_pairs_cost_lower (D : Data M Y K G anchor) (hK : 1 ≤ K)
    (b : Fin (K + 1) → F₂) (P : Finset (G × G)) (hP : P ⊆ directed univ) {A N : ℕ}
    (hclean : ∀ p ∈ P, ∃ selected : Free (anchor p.1),
      p.2.val ∈ targets A N
        (PaperP1.AnchoredWindowForcing.pivots (D.window p.1) selected).val.val (K + 1)
        (otherPrimes (PaperP1.AnchoredWindowForcing.pivots (D.window p.1)) selected))
    (hjoint : ∀ p ∈ P, Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (K + 1) ↦ p.1.val + i.val) (fun i : Fin (K + 1) ↦ p.2.val + i.val))) :
    (rate K) ^ 2 * P.card ≤ cost D b :=
  (selected_pairs_offsite_lower D hK b P hP hclean hjoint).trans
    (PaperP1.PositiveForcingCostLower.offsite_le_full_cost univ (cylinderProbability M)
      (indicator b) (force D b) (fun j _ ω ↦ force_hits D b j ω))

end PaperP1.AnchoredPrivateField
