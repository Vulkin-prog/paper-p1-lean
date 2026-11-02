module

public import PaperP1.Probability.SeededCenteredTruncation
public import PaperP1.Probability.FiniteCoupling

/-! # Exact positive counts of selected active pairs and a finite truncation inequality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActivePairCount

open Finset PaperP1.Algebra PaperP1.Probability

variable {Ω ι : Type*}

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def value (F : Finset (Finset ι)) (J : ι → Ω → Bool) (ω : Ω) : ℝ :=
  ∑ e ∈ F, ∏ x ∈ e, (indicatorValue (J x ω) : ℝ)

def active (F : Finset (Finset ι)) (J : ι → Ω → Bool) (ω : Ω) : Prop :=
  ∃ e ∈ F, ∀ x ∈ e, J x ω = true

theorem value_nonneg (F : Finset (Finset ι)) (J : ι → Ω → Bool) (ω : Ω) :
    0 ≤ value F J ω := sum_nonneg fun e _ ↦ indicator_product_nonneg J e ω

theorem value_eq_card (F : Finset (Finset ι)) (J : ι → Ω → Bool) (ω : Ω) :
    value F J ω = ((F.filter fun e ↦ ∀ x ∈ e, J x ω = true).card : ℝ) := by
  unfold value
  simp_rw [indicator_product_eq_indicator]
  exact sum_boole _ _

theorem active_iff_positive (F : Finset (Finset ι)) (J : ι → Ω → Bool) (ω : Ω) :
    active F J ω ↔ 0 < value F J ω := by
  rw [value_eq_card, Nat.cast_pos, card_pos]
  simp only [active, filter_nonempty_iff]

theorem indicator_le_value (F : Finset (Finset ι)) (J : ι → Ω → Bool) (ω : Ω) :
    (if active F J ω then (1 : ℝ) else 0) ≤ value F J ω := by
  by_cases h : active F J ω
  · rw [ite_eq_left h, value_eq_card]
    exact_mod_cast Nat.succ_le_of_lt (by simpa only [value_eq_card, Nat.cast_pos] using (active_iff_positive F J ω).mp h)
  · rw [ite_eq_right h]
    exact value_nonneg F J ω

theorem value_le_count_square [DecidableEq ι] (G : Finset ι) (F : Finset (Finset ι))
    (hF : F ⊆ G.powersetCard 2) (J : ι → Ω → Bool) (ω : Ω) :
    value F J ω ≤ (indicatorCount G J ω : ℝ) ^ 2 := by
  let w : ι → ℝ := fun x ↦ indicatorValue (J x ω)
  have hw : ∀ x, 0 ≤ w x := by intro x; dsimp [w]; cases J x ω <;> norm_num [indicatorValue]
  have hsum : (∑ x ∈ G, w x) = (indicatorCount G J ω : ℝ) := by
    rw [indicatorCount, Nat.cast_sum]
    apply sum_congr rfl
    intro x _
    dsimp [w]
    cases J x ω <;> norm_num [indicatorValue]
  have hle : value F J ω ≤ (∑ x ∈ G, w x) ^ 2 / 2 :=
    (sum_le_sum_of_subset_of_nonneg hF (fun e _ _ ↦ prod_nonneg fun x _ ↦ hw x)).trans
      (by simpa only [SubsetPowerSums.elementary, Nat.factorial_two, Nat.cast_ofNat] using
        ElementarySymmetricBound.elementary_le_power_div w hw G 2)
  rw [hsum] at hle
  nlinarith only [hle, sq_nonneg (indicatorCount G J ω : ℝ)]

variable [Fintype Ω]

theorem mean_eq (P : FiniteProbability Ω) (F : Finset (Finset ι)) (J : ι → Ω → Bool) :
    finiteExpectation P.weight (value F J) = ∑ e ∈ F, finiteJointMoment P J e := by
  unfold value finiteJointMoment
  exact finiteExpectation_sum _ _ _

theorem truncation (P : FiniteProbability Ω) (X Z : Ω → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (hZ : ∀ ω, 0 ≤ Z ω) (hXZ : ∀ ω, X ω ≤ Z ω ^ 2)
    (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 2 ≤ m) :
    finiteExpectation P.weight X ≤
      R ^ 2 * finiteExpectation P.weight (fun ω ↦ if 0 < X ω then 1 else 0) +
        finiteExpectation P.weight (fun ω ↦ Z ω ^ m) / R ^ (m - 2) := by
  calc
    _ ≤ finiteExpectation P.weight (fun ω ↦
        R ^ 2 * (if 0 < X ω then 1 else 0) + Z ω ^ m / R ^ (m - 2)) := by
      apply finiteExpectation_mono P
      intro ω
      have ht : 0 ≤ Z ω ^ m / R ^ (m - 2) := div_nonneg (pow_nonneg (hZ ω) _) (pow_nonneg hR.le _)
      by_cases hx : 0 < X ω
      · rw [ite_eq_left hx, mul_one]
        by_cases hz : Z ω ≤ R
        · have hs := (hXZ ω).trans (pow_le_pow_left₀ (hZ ω) hz 2)
          linarith only [hs, ht]
        · have hpow : Z ω ^ 2 ≤ Z ω ^ m / R ^ (m - 2) := by
            apply (le_div_iff₀ (pow_pos hR _)).mpr
            calc
              _ ≤ Z ω ^ 2 * Z ω ^ (m - 2) := mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ hR.le (le_of_not_ge hz) _) (sq_nonneg _)
              _ = _ := by rw [← pow_add, show 2 + (m - 2) = m by omega]
          have hs := (hXZ ω).trans hpow
          linarith only [hs, sq_nonneg R]
      · rw [ite_eq_right hx, mul_zero, zero_add]
        have hz : X ω = 0 := le_antisymm (not_lt.mp hx) (hX ω)
        simpa only [hz] using ht
    _ = _ := by
      have hdiv : finiteExpectation P.weight (fun ω ↦ Z ω ^ m / R ^ (m - 2)) =
          finiteExpectation P.weight (fun ω ↦ Z ω ^ m) / R ^ (m - 2) := by
        simpa only [div_eq_mul_inv] using
          finiteExpectation_mul_const P.weight (fun ω ↦ Z ω ^ m) (R ^ (m - 2))⁻¹
      rw [finiteExpectation_add, finiteExpectation_const_mul, hdiv]

end PaperP1.ActivePairCount
