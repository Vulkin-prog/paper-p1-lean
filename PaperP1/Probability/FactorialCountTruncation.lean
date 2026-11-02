module

public import PaperP1.Probability.StoppedFiniteLaw
public import PaperP1.Probability.SubsetFactorials
public import Mathlib.Tactic.FieldSimp

/-! # Finite count-law reconstruction from fixed factorial moments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FactorialCountTruncation

open Finset PaperP1.Algebra PaperP1.Probability

variable {Ω ι : Type*} [Fintype Ω] [LinearOrder ι]

def moment (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool) (r : ℕ) : ℝ :=
  finiteExpectation P.weight (fun ω ↦ ((indicatorCount G J ω).descFactorial r : ℝ))

def polynomial (a : ℕ → ℝ) (k : ℕ) : SignedLaw ℝ :=
  ∑ r ∈ range k, scalar (a r / (r.factorial : ℝ)) * forwardDifference ^ r

omit [LinearOrder ι] in
theorem moment_eq_joint (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool) (r : ℕ) :
    moment G P J r = (r.factorial : ℝ) * ∑ I ∈ G.powersetCard r, finiteJointMoment P J I := by
  unfold moment
  simp_rw [factorial_subset_expansion]
  rw [finiteExpectation_const_mul, finiteExpectation_sum]
  rfl

theorem boundary_card (G : Finset ι) (k : ℕ) (hk : 1 ≤ k) {I : Finset ι}
    (hI : I ∈ boundarySets G (fun A ↦ A.card < k)) : I ∈ G.powersetCard k := by
  classical
  obtain ⟨hIG, hb⟩ := mem_filter.mp hI
  have hn := orderedBoundary_nonempty (by simp only [card_empty]; omega : (∅ : Finset ι).card < k) hb
  have hc : (properPrefix I).card + 1 = I.card := by
    rw [properPrefix_eq_erase_max I hn]
    exact card_erase_add_one (I.max'_mem hn)
  have hp := hb.2
  exact mem_powersetCard.mpr ⟨mem_powerset.mp hIG, by have h := hb.1; omega⟩

omit [LinearOrder ι] in
theorem retained_layer (G : Finset ι) (k r : ℕ) (hr : r ∈ range k) :
    (retainedSets G (fun A ↦ A.card < k)).filter (fun I ↦ I.card = r) = G.powersetCard r := by
  classical
  ext I
  simp only [retainedSets, mem_filter, mem_powerset, mem_powersetCard]
  constructor
  · rintro ⟨⟨hsub, _⟩, hcard⟩; exact ⟨hsub, hcard⟩
  · rintro ⟨hsub, hcard⟩; exact ⟨⟨hsub, hcard ▸ mem_range.mp hr⟩, hcard⟩

omit [LinearOrder ι] in
theorem retained_eq_polynomial (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool) (k : ℕ) :
    retainedCountReference G (fun A ↦ A.card < k) P J = polynomial (moment G P J) k := by
  classical
  unfold retainedCountReference polynomial
  have hsize (I : Finset ι) (hI : I ∈ retainedSets G (fun A ↦ A.card < k)) : I.card ∈ range k := by
    have hm : I ⊆ G ∧ I.card < k := by
      simpa only [retainedSets, mem_filter, mem_powerset] using hI
    exact mem_range.mpr hm.2
  rw [← sum_fiberwise_of_maps_to (s := retainedSets G (fun A ↦ A.card < k)) (t := range k) (g := fun I : Finset ι ↦ I.card) hsize]
  apply sum_congr rfl
  intro r hr
  rw [retained_layer G k r hr]
  calc
    _ = ∑ I ∈ G.powersetCard r, scalar (finiteJointMoment P J I) * forwardDifference ^ r := by
      apply sum_congr rfl
      intro I hI
      rw [(mem_powersetCard.mp hI).2]
    _ = scalar (∑ I ∈ G.powersetCard r, finiteJointMoment P J I) * forwardDifference ^ r := by
      rw [← sum_mul, ← map_sum]
    _ = _ := by
      rw [moment_eq_joint]
      congr 2
      field_simp [show (r.factorial : ℝ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero r]

theorem remainder_bound (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool)
    (k : ℕ) (hk : 1 ≤ k) :
    l1Norm (countLaw G P.weight J - polynomial (moment G P J) k) ≤
      (2 : ℝ) ^ k / (k.factorial : ℝ) * moment G P J k := by
  have hD : Hereditary (fun A : Finset ι ↦ A.card < k) := fun _ _ hsub hI ↦ (card_le_card hsub).trans_lt hI
  have he : (∅ : Finset ι).card < k := by simp only [card_empty]; omega
  rw [← retained_eq_polynomial G P J k]
  calc
    _ ≤ ∑ I ∈ boundarySets G (fun A ↦ A.card < k), (2 : ℝ) ^ I.card * finiteJointMoment P J I :=
      stopped_finite_count_l1_bound G _ P J hD he
    _ ≤ ∑ I ∈ G.powersetCard k, (2 : ℝ) ^ I.card * finiteJointMoment P J I :=
      sum_le_sum_of_subset_of_nonneg (fun _ hI ↦ boundary_card G k hk hI)
        (fun I _ _ ↦ mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) I.card) (finiteJointMoment_nonneg P J I))
    _ = (2 : ℝ) ^ k * ∑ I ∈ G.powersetCard k, finiteJointMoment P J I := by
      rw [mul_sum]
      exact sum_congr rfl (fun I hI ↦ by rw [(mem_powersetCard.mp hI).2])
    _ = _ := by
      rw [moment_eq_joint]
      field_simp [show (k.factorial : ℝ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero k]

theorem polynomial_difference (a b : ℕ → ℝ) (k : ℕ) :
    l1Norm (polynomial a k - polynomial b k) ≤
      ∑ r ∈ range k, (2 : ℝ) ^ r / (r.factorial : ℝ) * |a r - b r| := by
  unfold polynomial
  rw [← sum_sub_distrib]
  apply (l1Norm_sum _ _).trans
  apply sum_le_sum
  intro r _
  have heq : scalar (a r / (r.factorial : ℝ)) * forwardDifference ^ r -
      scalar (b r / (r.factorial : ℝ)) * forwardDifference ^ r =
      scalar ((a r - b r) / (r.factorial : ℝ)) * forwardDifference ^ r := by
    rw [sub_div, map_sub, sub_mul]
  rw [heq]
  calc
    _ ≤ l1Norm (scalar ((a r - b r) / (r.factorial : ℝ))) * l1Norm (forwardDifference ^ r) := l1Norm_mul _ _
    _ ≤ |(a r - b r) / (r.factorial : ℝ)| * (2 : ℝ) ^ r := by
      rw [l1Norm_scalar]
      exact mul_le_mul_of_nonneg_left (l1Norm_forwardDifference_pow_le r) (abs_nonneg _)
    _ = _ := by rw [abs_div, abs_of_nonneg (Nat.cast_nonneg r.factorial : (0 : ℝ) ≤ r.factorial)]; ring

end PaperP1.FactorialCountTruncation
