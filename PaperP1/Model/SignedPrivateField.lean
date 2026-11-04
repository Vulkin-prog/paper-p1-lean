module

public import PaperP1.Model.SignedPrivatePalmForcing
public import PaperP1.Probability.ForcingCoordinateCost
public import Mathlib.Algebra.BigOperators.Fin

/-! # The actual finite signed field and its specified private-pivot cost

Every retained left boundary carries both signs and all excesses `0..E`.
The maximal support certifies privacy; the forcing prescribes only the
source's actual word. The Palm law and directed support are proved here,
rather than postulated as a coupling interface.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedPrivateField

open Finset PaperP1.Algebra PaperP1.Probability PaperP1.Model PaperP1.Arithmetic
  PaperP1.PrivateValueSystem PaperP1.PrivatePivotGeometry PaperP1.PrivatePrimeForcing
  PaperP1.SignedExactWords PaperP1.SignedPrivatePalmForcing PaperP1.UniformFubini
  PaperP1.OddPrimePivot

local instance signedPrivateFieldDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

abbrev Index (J : Finset ℕ) (E : ℕ) := J × (Fin (E + 1) × F₂)

structure Data (M Y L E : ℕ) (J : Finset ℕ) : Prop where
  length_pos : 1 ≤ L
  boundary_pos : ∀ j ∈ J, 0 < j
  cutoff : ∀ j ∈ J, j + (L + E + 2) ≤ M + 1
  small_cutoff : L + E + 2 ≤ Y
  good : ∀ j ∈ J, ∀ i : Fin (L + E + 2), Y < largestOddPrime (j + i.val)

variable {M Y L E : ℕ} {J : Finset ℕ}

theorem actual_good (D : Data M Y L E J) (a : Index J E) :
    ∀ i : Fin (L + a.2.1.val + 2), Y < largestOddPrime (a.1.val + i.val) :=
  actual_support_of_maximal (by have := a.2.1.isLt; omega) (D.good a.1.val a.1.property)

theorem actual_cutoff (D : Data M Y L E J) (a : Index J E) :
    a.1.val + (L + a.2.1.val + 2) ≤ M + 1 := by
  have := D.cutoff a.1.val a.1.property
  have := a.2.1.isLt
  omega

theorem small_pos (D : Data M Y L E J) : 1 ≤ Y := by
  have := D.small_cutoff
  omega

def pivots (D : Data M Y L E J) (a : Index J E) :
    Fin (L + a.2.1.val + 2) → PrimeUpTo M :=
  cylinderPivot (D.boundary_pos a.1.val a.1.property) (actual_cutoff D a)
    (fun i ↦ (small_pos D).trans_lt (actual_good D a i))

theorem pivots_basis (D : Data M Y L E J) (a : Index J E)
    (i : Fin (L + a.2.1.val + 2)) :
    valueSystem M (fun k : Fin (L + a.2.1.val + 2) ↦ a.1.val + k.val)
      (Pi.single (pivots D a i) 1) = Pi.single i 1 := by
  apply cylinderPivot_basis
  intro k
  exact (by have := D.small_cutoff; have := a.2.1.isLt; omega : L + a.2.1.val + 2 ≤ Y).trans
    (actual_good D a k).le

def force (D : Data M Y L E J) (a : Index J E) (ω : SampleSpace M) : SampleSpace M :=
  forceWord (fun i : Fin (L + a.2.1.val + 2) ↦ a.1.val + i.val)
    (pivots D a) (signedExactWord L a.2.1.val a.2.2) ω

def indicator (M L : ℕ) (a : Index J E) (ω : SampleSpace M) : Bool :=
  decide (SignedExactMark (valueBit ω) (a.1.val + 1) L a.2.1.val a.2.2)

theorem force_hits (D : Data M Y L E J) (a : Index J E) (ω : SampleSpace M) :
    indicator M L a (force D a ω) = true := by
  exact decide_eq_true (signedForcing_hits D.length_pos (pivots D a)
    (pivots_basis D a) a.2.2 ω)

theorem indicator_marginal (D : Data M Y L E J) (a : Index J E) :
    exactMarginal (cylinderProbability M) (indicator M L) a = signedMarkRate L a.2.1.val := by
  have h := actual_signed_probability (D.boundary_pos a.1.val a.1.property) D.length_pos
    (actual_cutoff D a) (small_pos D)
    (by have := D.small_cutoff; have := a.2.1.isLt; omega) (actual_good D a) a.2.2
  simpa only [exactMarginal, cylinderProbability, indicator, indicatorValue,
    decide_eq_true_eq, average] using h

theorem total_marginal (D : Data M Y L E J) :
    (∑ a : Index J E, exactMarginal (cylinderProbability M) (indicator M L) a) =
      (J.card : ℝ) * ((2 ^ L : ℝ)⁻¹ * (1 - (2 ^ (E + 1) : ℝ)⁻¹)) := by
  have ht : (∑ e : Fin (E + 1), ∑ _s : F₂, signedMarkRate L e.val) =
      (2 ^ L : ℝ)⁻¹ * (1 - (2 ^ (E + 1) : ℝ)⁻¹) := by
    rw [Fin.sum_univ_eq_sum_range (fun e ↦ ∑ _s : F₂, signedMarkRate L e), sum_signedMarkRate]
  simp only [sum_const, card_univ, nsmul_eq_mul] at ht
  simp only [indicator_marginal D, Index, Fintype.sum_prod_type, sum_const,
    card_univ, Fintype.card_coe, nsmul_eq_mul]
  rw [ht]

theorem total_marginal_le (D : Data M Y L E J) :
    (∑ a : Index J E, exactMarginal (cylinderProbability M) (indicator M L) a) ≤
      (J.card : ℝ) * (2 ^ L : ℝ)⁻¹ := by
  rw [total_marginal D]
  have h : (1 - (2 ^ (E + 1) : ℝ)⁻¹) ≤ 1 := sub_le_self _ (by positivity)
  have h' := mul_le_mul_of_nonneg_left h
    (by positivity : (0 : ℝ) ≤ (J.card : ℝ) * (2 ^ L : ℝ)⁻¹)
  simpa only [mul_assoc, mul_one] using h'

theorem weighted_palm (D : Data M Y L E J) (a : Index J E) (f : SampleSpace M → ℝ) :
    exactMarginal (cylinderProbability M) (indicator M L) a *
      finiteExpectation (cylinderProbability M).weight (fun ω ↦ f (force D a ω)) =
    finiteExpectation (cylinderProbability M).weight
      (fun ω ↦ indicatorValue (indicator M L a ω) * f ω) := by
  have h := uniform_conditional_expectation
    (fun i : Fin (L + a.2.1.val + 2) ↦ a.1.val + i.val)
    (pivots D a) (pivots_basis D a) (signedExactWord L a.2.1.val a.2.2) f
  have hc : (Fintype.card (Fin (L + a.2.1.val + 2) → F₂) : ℝ)⁻¹ =
      signedMarkRate L a.2.1.val := by
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow,
      Nat.cast_ofNat, signedMarkRate]
  rw [hc] at h
  simp only [finite_signedWord_iff D.length_pos] at h
  have he : (fun ω : SampleSpace M ↦
      if SignedExactMark (valueBit ω) (a.1.val + 1) L a.2.1.val a.2.2 then f ω else 0) =
      (fun ω ↦ indicatorValue (indicator M L a ω) * f ω) := by
    funext ω
    by_cases hh : SignedExactMark (valueBit ω) (a.1.val + 1) L a.2.1.val a.2.2
    all_goals simp [indicator, indicatorValue, hh]
  rw [he] at h
  rw [indicator_marginal D a]
  simpa only [average, cylinderProbability, force, mul_comm] using
    (eq_div_iff (signedMarkRate_pos L a.2.1.val).ne').mp h

def footprint (D : Data M Y L E J) (a : Index J E) : Finset (Index J E) :=
  univ.filter fun b ↦ ∃ i : Fin (L + a.2.1.val + 2), ∃ k : Fin (L + E + 2),
    (pivots D a i).val.val ∣ b.1.val + k.val

theorem outside_footprint (D : Data M Y L E J) (a b : Index J E)
    (hb : b ∉ footprint D a) (ω : SampleSpace M) :
    indicator M L b (force D a ω) = indicator M L b ω := by
  have he : valueSystem M (fun k : Fin (L + b.2.1.val + 2) ↦ b.1.val + k.val)
      (force D a ω) =
      valueSystem M (fun k : Fin (L + b.2.1.val + 2) ↦ b.1.val + k.val) ω := by
    funext k
    change valueBit (force D a ω) (b.1.val + k.val) = valueBit ω (b.1.val + k.val)
    unfold force
    apply forceWord_preserves_value
    intro i hdiv
    have hk : k.val < L + E + 2 := by have := k.isLt; have := b.2.1.isLt; omega
    exact hb (mem_filter.mpr ⟨mem_univ _, ⟨i, ⟨k.val, hk⟩, hdiv⟩⟩)
  have hi : SignedExactMark (valueBit (force D a ω)) (b.1.val + 1) L b.2.1.val b.2.2 ↔
      SignedExactMark (valueBit ω) (b.1.val + 1) L b.2.1.val b.2.2 := by
    rw [← finite_signedWord_iff D.length_pos, ← finite_signedWord_iff D.length_pos, he]
  simp only [indicator, hi]

def cost (D : Data M Y L E J) : ℝ :=
  ForcingCoordinateCost.cost univ (cylinderProbability M) (indicator M L) (force D)

theorem cost_diagonal_decomposition (D : Data M Y L E J) :
    cost D = (∑ a : Index J E, (signedMarkRate L a.2.1.val) ^ 2) +
      ∑ a : Index J E, signedMarkRate L a.2.1.val *
        ForcingCoordinateCost.offsiteCost univ (cylinderProbability M) (indicator M L) (force D) a := by
  simpa only [cost, indicator_marginal D] using
    ForcingCoordinateCost.exact_diagonal_decomposition univ (cylinderProbability M)
      (indicator M L) (force D) (fun a _ ω ↦ force_hits D a ω)

/-- The actual signed field discharges the full Palm and preservation hypotheses. -/
theorem cost_footprint_upper (D : Data M Y L E J) :
    cost D ≤ (∑ a : Index J E, (signedMarkRate L a.2.1.val) ^ 2) +
      ∑ a : Index J E, ∑ b ∈ (univ.erase a) ∩ footprint D a,
        (signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val +
          ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) a b) := by
  have h := ForcingCoordinateCost.total_footprint_upper univ (cylinderProbability M)
    (indicator M L) (force D) (footprint D) (fun a _ ω ↦ force_hits D a ω)
    (fun a _ b _ hb ω ↦ outside_footprint D a b hb ω)
    (fun a _ b _ ↦ weighted_palm D a (fun ω ↦ indicatorValue (indicator M L b ω)))
  simpa only [cost, indicator_marginal D] using h

end PaperP1.SignedPrivateField
