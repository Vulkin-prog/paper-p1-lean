module

public import PaperP1.Asymptotics.CriticalSequentialPairMass
public import PaperP1.Model.SelectedPairBranchingTuples

/-! # The literal selected single-pair tuple mass at every growing critical order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedPairCriticalMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CriticalFreshBranchingBudget

def amplitude (E : Finset (Finset ℕ)) (L : ℕ) : ℝ := 2 * ∑ e ∈ E, infiniteJointMoment L e

theorem amplitude_nonneg (E : Finset (Finset ℕ)) (L : ℕ) : 0 ≤ amplitude E L :=
  mul_nonneg (by norm_num) (sum_nonneg fun e _ ↦ infiniteJointMoment_nonneg L e)

theorem uniform_bound (K C : ℝ) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ m : ℕ, 2 ≤ m →
      (m : ℝ) ≤ orderCap K N → ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ E : Finset (Finset ℕ), E ⊆ (dyadicBlock N).powersetCard 2 →
      (∀ e ∈ E, 0 < runRelativeNullity L e) → ∀ k : ℕ, k + 2 ≤ m →
        |SelectedPairBranchingTuples.mass (dyadicBlock N) E N L k -
          ((k + 2).choose 2 : ℝ) * ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ k * amplitude E L| ≤
        (((k + 2).choose 2 : ℝ) * ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ k * amplitude E L) *
          ((k : ℝ) * freshEnvelope K N / N) := by
  obtain ⟨N₀, hN₀, hu⟩ := CriticalSequentialPairMass.uniform_pair K C hK
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN m hm horder L hband E hE hdep k hkm
  let ellMean := (N : ℝ) * (2 ^ L : ℝ)⁻¹
  let d := (k : ℝ) * freshEnvelope K N / N
  have hsum : |(∑ e ∈ E, SequentialRetainedWindows.mass N L e k) -
      ellMean ^ k * ∑ e ∈ E, infiniteJointMoment L e| ≤
      (ellMean ^ k * ∑ e ∈ E, infiniteJointMoment L e) * d := by
    calc
      _ = |∑ e ∈ E, (SequentialRetainedWindows.mass N L e k - ellMean ^ k * infiniteJointMoment L e)| := by
        rw [sum_sub_distrib, ← mul_sum]
      _ ≤ ∑ e ∈ E, |SequentialRetainedWindows.mass N L e k - ellMean ^ k * infiniteJointMoment L e| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ E, (ellMean ^ k * infiniteJointMoment L e) * d := by
        apply sum_le_sum
        intro e he
        exact hu N hN m hm horder L hband e (mem_powersetCard.mp (hE he)).1
          (mem_powersetCard.mp (hE he)).2 k hkm
      _ = _ := by rw [← sum_mul, ← mul_sum]
  rw [SelectedPairBranchingTuples.mass_exact (by omega) Subset.rfl hE hdep]
  have heq : ((k + 2).choose 2 : ℝ) * (2 * ∑ e ∈ E, SequentialRetainedWindows.mass N L e k) -
      ((k + 2).choose 2 : ℝ) * ellMean ^ k * amplitude E L =
      (((k + 2).choose 2 : ℝ) * 2) *
        ((∑ e ∈ E, SequentialRetainedWindows.mass N L e k) - ellMean ^ k * ∑ e ∈ E, infiniteJointMoment L e) := by
    unfold amplitude
    ring
  change |((k + 2).choose 2 : ℝ) * (2 * ∑ e ∈ E, SequentialRetainedWindows.mass N L e k) -
      ((k + 2).choose 2 : ℝ) * ellMean ^ k * amplitude E L| ≤ _
  rw [heq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k + 2).choose 2 : ℝ) * 2)]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by unfold amplitude; ring)

theorem uniform_numeric_bound (K C ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ m : ℕ, 2 ≤ m →
      (m : ℝ) ≤ orderCap K N → ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ E : Finset (Finset ℕ), E ⊆ (dyadicBlock N).powersetCard 2 →
      (∀ e ∈ E, 0 < runRelativeNullity L e) → ∀ k : ℕ, k + 2 ≤ m →
        |SelectedPairBranchingTuples.mass (dyadicBlock N) E N L k -
          ((k + 2).choose 2 : ℝ) * ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ k * amplitude E L| ≤
        (((k + 2).choose 2 : ℝ) * ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ k * amplitude E L) *
          (N : ℝ) ^ (-1 / 3 + ε) := by
  obtain ⟨NB, _hNB, hb⟩ := uniform_bound K C hK
  obtain ⟨ND, _hND, hd⟩ := uniform_small_budget K ε hK hε
  refine ⟨max 3 (max NB ND), by omega, ?_⟩
  intro N hN m hm horder L hband E hE hdep k hkm
  have hbudget := (hd N (by omega)).2 m horder
  have hk : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by omega)
  have hlocal : (k : ℝ) * freshEnvelope K N / N ≤ (N : ℝ) ^ (-1 / 3 + ε) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hk (freshEnvelope_pos K N).le)
      (Nat.cast_nonneg N)).trans hbudget
  exact (hb N (by omega) m hm horder L hband E hE hdep k hkm).trans
    (mul_le_mul_of_nonneg_left hlocal (mul_nonneg (by positivity) (amplitude_nonneg E L)))

end PaperP1.SelectedPairCriticalMass
