module

public import PaperP1.Probability.ActivePairCount

/-! # A finite joint row bound controls every fixed count moment after a seed -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeededCountMoments

open Finset PaperP1.Algebra PaperP1.Probability

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def moment (P : FiniteProbability Ω) (J : ι → Ω → Bool) (G I : Finset ι) (k : ℕ) : ℝ :=
  finiteExpectation P.weight (fun ω ↦ (∏ x ∈ I, (indicatorValue (J x ω) : ℝ)) *
    (∑ x ∈ G, (indicatorValue (J x ω) : ℝ)) ^ k)

omit [Fintype Ω] in
theorem insert_product (J : ι → Ω → Bool) (I : Finset ι) (y : ι) (ω : Ω) :
    (∏ x ∈ I, (indicatorValue (J x ω) : ℝ)) * indicatorValue (J y ω) =
      ∏ x ∈ insert y I, (indicatorValue (J x ω) : ℝ) := by
  rw [indicator_product_eq_indicator J I, indicator_product_eq_indicator J (insert y I)]
  by_cases hi : ∀ x ∈ I, J x ω = true <;> by_cases hy : J y ω = true <;>
    simp [hi, hy, indicatorValue]

omit [DecidableEq ι] in
theorem zero (P : FiniteProbability Ω) (J : ι → Ω → Bool) (G I : Finset ι) :
    moment P J G I 0 = finiteJointMoment P J I := by simp only [moment, pow_zero, mul_one, finiteJointMoment]

theorem succ (P : FiniteProbability Ω) (J : ι → Ω → Bool) (G I : Finset ι) (k : ℕ) :
    moment P J G I (k + 1) = ∑ y ∈ G, moment P J G (insert y I) k := by
  unfold moment
  rw [← finiteExpectation_sum]
  congr 1
  funext ω
  calc
    _ = ((∏ x ∈ I, (indicatorValue (J x ω) : ℝ)) * (∑ x ∈ G, (indicatorValue (J x ω) : ℝ)) ^ k) *
        (∑ y ∈ G, (indicatorValue (J y ω) : ℝ)) := by rw [pow_succ]; ring
    _ = ∑ y ∈ G, ((∏ x ∈ I, (indicatorValue (J x ω) : ℝ)) *
        (∑ x ∈ G, (indicatorValue (J x ω) : ℝ)) ^ k) * indicatorValue (J y ω) := mul_sum _ _ _
    _ = _ := by
      apply sum_congr rfl
      intro y _
      rw [← insert_product]
      ring

theorem bound (P : FiniteProbability Ω) (J : ι → Ω → Bool) (G : Finset ι)
    (k r : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hrow : ∀ I : Finset ι, I ⊆ G → I.Nonempty → I.card ≤ r + k →
      (∑ y ∈ G, finiteJointMoment P J (insert y I)) ≤ A * finiteJointMoment P J I)
    (I : Finset ι) (hIG : I ⊆ G) (hI : I.Nonempty) (hcard : I.card ≤ r) :
    moment P J G I k ≤ A ^ k * finiteJointMoment P J I := by
  induction k generalizing r I with
  | zero => simp only [zero, pow_zero, one_mul, le_refl]
  | succ k ih =>
    rw [succ]
    calc
      _ ≤ ∑ y ∈ G, A ^ k * finiteJointMoment P J (insert y I) := by
        apply sum_le_sum
        intro y hy
        exact ih (r + 1) (fun T hTG hT hc ↦ hrow T hTG hT (by omega)) (insert y I)
          (insert_subset_iff.mpr ⟨hy, hIG⟩) (insert_nonempty _ _) ((card_insert_le _ _).trans (by omega))
      _ = A ^ k * ∑ y ∈ G, finiteJointMoment P J (insert y I) := (mul_sum _ _ _).symm
      _ ≤ A ^ k * (A * finiteJointMoment P J I) :=
        mul_le_mul_of_nonneg_left (hrow I hIG hI (by omega)) (pow_nonneg hA _)
      _ = _ := by rw [pow_succ]; ring

theorem selected_pair_power (P : FiniteProbability Ω) (J : ι → Ω → Bool) (G : Finset ι)
    (F : Finset (Finset ι)) (hF : F ⊆ G.powersetCard 2) (r : ℕ) (hr : 1 ≤ r)
    (A : ℝ) (hA : 0 ≤ A)
    (hrow : ∀ I : Finset ι, I ⊆ G → I.Nonempty → I.card ≤ 2 + 2 * (r - 1) →
      (∑ y ∈ G, finiteJointMoment P J (insert y I)) ≤ A * finiteJointMoment P J I) :
    finiteExpectation P.weight (fun ω ↦ ActivePairCount.value F J ω ^ r) ≤
      A ^ (2 * (r - 1)) * ∑ e ∈ F, finiteJointMoment P J e := by
  calc
    _ ≤ finiteExpectation P.weight (fun ω ↦ ActivePairCount.value F J ω *
        (∑ x ∈ G, (indicatorValue (J x ω) : ℝ)) ^ (2 * (r - 1))) := by
      apply finiteExpectation_mono P
      intro ω
      have hS : (∑ x ∈ G, (indicatorValue (J x ω) : ℝ)) = (indicatorCount G J ω : ℝ) := by
        rw [indicatorCount, Nat.cast_sum]
        apply sum_congr rfl
        intro x _
        cases J x ω <;> norm_num [indicatorValue]
      have hle := ActivePairCount.value_le_count_square G F hF J ω
      rw [← hS] at hle
      calc
        _ = ActivePairCount.value F J ω * ActivePairCount.value F J ω ^ (r - 1) := by
          rw [← pow_succ', show r - 1 + 1 = r by omega]
        _ ≤ ActivePairCount.value F J ω * ((∑ x ∈ G, (indicatorValue (J x ω) : ℝ)) ^ 2) ^ (r - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ActivePairCount.value_nonneg F J ω) hle _) (ActivePairCount.value_nonneg F J ω)
        _ = _ := by rw [pow_mul]
    _ = ∑ e ∈ F, moment P J G e (2 * (r - 1)) := by
      unfold ActivePairCount.value moment
      simp_rw [sum_mul]
      exact finiteExpectation_sum _ _ _
    _ ≤ ∑ e ∈ F, A ^ (2 * (r - 1)) * finiteJointMoment P J e := by
      apply sum_le_sum
      intro e he
      obtain ⟨heG, hecard⟩ := mem_powersetCard.mp (hF he)
      exact bound P J G (2 * (r - 1)) 2 A hA hrow e heG (card_pos.mp (by omega)) hecard.le
    _ = _ := (mul_sum _ _ _).symm

omit [Fintype Ω] in
theorem value_le_count_power (G : Finset ι) (F : Finset (Finset ι)) (s : ℕ)
    (hF : F ⊆ G.powersetCard s) (J : ι → Ω → Bool) (ω : Ω) :
    ActivePairCount.value F J ω ≤ (indicatorCount G J ω : ℝ) ^ s := by
  let w : ι → ℝ := fun x ↦ indicatorValue (J x ω)
  have hw : ∀ x, 0 ≤ w x := by intro x; dsimp [w]; cases J x ω <;> norm_num [indicatorValue]
  have hsum : (∑ x ∈ G, w x) = (indicatorCount G J ω : ℝ) := by
    rw [indicatorCount, Nat.cast_sum]
    apply sum_congr rfl
    intro x _
    dsimp [w]
    cases J x ω <;> norm_num [indicatorValue]
  have hf : (1 : ℝ) ≤ s.factorial := by exact_mod_cast Nat.factorial_pos s
  calc
    _ ≤ SubsetPowerSums.elementary w G s :=
      sum_le_sum_of_subset_of_nonneg hF (fun e _ _ ↦ prod_nonneg fun x _ ↦ hw x)
    _ ≤ (∑ x ∈ G, w x) ^ s / s.factorial := ElementarySymmetricBound.elementary_le_power_div w hw G s
    _ ≤ (∑ x ∈ G, w x) ^ s := div_le_self (pow_nonneg (sum_nonneg fun x _ ↦ hw x) _) hf
    _ = _ := by rw [hsum]

theorem selected_family_power (P : FiniteProbability Ω) (J : ι → Ω → Bool) (G : Finset ι)
    (F : Finset (Finset ι)) (s : ℕ) (hs : 1 ≤ s) (hF : F ⊆ G.powersetCard s) (r : ℕ) (hr : 1 ≤ r)
    (A : ℝ) (hA : 0 ≤ A)
    (hrow : ∀ I : Finset ι, I ⊆ G → I.Nonempty → I.card ≤ s + s * (r - 1) →
      (∑ y ∈ G, finiteJointMoment P J (insert y I)) ≤ A * finiteJointMoment P J I) :
    finiteExpectation P.weight (fun ω ↦ ActivePairCount.value F J ω ^ r) ≤
      A ^ (s * (r - 1)) * ∑ e ∈ F, finiteJointMoment P J e := by
  calc
    _ ≤ finiteExpectation P.weight (fun ω ↦ ActivePairCount.value F J ω *
        (∑ x ∈ G, (indicatorValue (J x ω) : ℝ)) ^ (s * (r - 1))) := by
      apply finiteExpectation_mono P
      intro ω
      have hS : (∑ x ∈ G, (indicatorValue (J x ω) : ℝ)) = (indicatorCount G J ω : ℝ) := by
        rw [indicatorCount, Nat.cast_sum]
        apply sum_congr rfl
        intro x _
        cases J x ω <;> norm_num [indicatorValue]
      have hle := value_le_count_power G F s hF J ω
      rw [← hS] at hle
      calc
        _ = ActivePairCount.value F J ω * ActivePairCount.value F J ω ^ (r - 1) := by
          rw [← pow_succ', show r - 1 + 1 = r by omega]
        _ ≤ ActivePairCount.value F J ω * ((∑ x ∈ G, (indicatorValue (J x ω) : ℝ)) ^ s) ^ (r - 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ActivePairCount.value_nonneg F J ω) hle _) (ActivePairCount.value_nonneg F J ω)
        _ = _ := by rw [pow_mul]
    _ = ∑ e ∈ F, moment P J G e (s * (r - 1)) := by
      unfold ActivePairCount.value moment
      simp_rw [sum_mul]
      exact finiteExpectation_sum _ _ _
    _ ≤ ∑ e ∈ F, A ^ (s * (r - 1)) * finiteJointMoment P J e := by
      apply sum_le_sum
      intro e he
      obtain ⟨heG, hecard⟩ := mem_powersetCard.mp (hF he)
      exact bound P J G (s * (r - 1)) s A hA hrow e heG (card_pos.mp (by omega)) hecard.le
    _ = _ := (mul_sum _ _ _).symm


end PaperP1.SeededCountMoments
