module

public import PaperP1.Asymptotics.ShiftedAsymmetricCriticalFamily

/-! # The printed radius-one version of the asymmetric profile cannot hold

This obstruction concerns companion T1.10 with the article's literal
radius-one definition of nonalignment. The family becomes aligned after
enlarging that radius. No conclusion of the main article is refuted here,
and the profile with the enlarged exclusion is not asserted or assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricAlignmentScopeObstruction

open PaperP1.AsymmetricShiftedWitness PaperP1.ShiftedAsymmetricPopulation
  PaperP1.ShiftedAsymmetricCriticalFamily

def profile (N L H : ℕ) : ℝ := by
  classical
  exact ∑ p ∈ ((PaperP1.Model.dyadicBlock N) ×ˢ (PaperP1.Model.dyadicBlock N)).filter
    (fun p ↦ ¬CompressedTargetAlignment.Aligned 1 p.1 p.2 L),
    ((2 : ℝ) ^ AsymmetricEvenLoss.loss H
      (Finset.Icc p.1 (p.1 + 3 * (L + 1))) p.2 L - 1)

theorem profile_eq_total (N H k : ℕ) : profile N (3 * k) H = total N H k := rfl

theorem violates_printed_exponent (A : ℝ) (K₀ : ℕ) :
    ∃ k ≥ K₀, 2 ≤ k ∧
      ∀ H ≥ 3, A * (dyadicScale k : ℝ) ^ ((31 / 24 : ℝ) + 1 / 48) <
        total (dyadicScale k) H k := by
  obtain ⟨Kw, hw⟩ := width_constraints
  obtain ⟨Ka, ha⟩ := HalfCountSchedule.factor_absorption
    (16 * A * (6 : ℝ) ^ (21 / 16 : ℝ)) (21 / 16) (1 / 48) (by norm_num)
  let k := max K₀ (max Kw (max Ka 2))
  have hk : K₀ ≤ k := by dsimp [k]; omega
  have hk2 : 2 ≤ k := by dsimp [k]; omega
  have hkw : Kw ≤ k := by dsimp [k]; omega
  have hka : Ka ≤ scale k := (show Ka ≤ k by dsimp [k]; omega).trans (index_le_scale k)
  have hp : (0 : ℝ) < (scale k : ℝ) ^ (4 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast scale_pos k) _
  have habs := ha (scale k) hka
  have he : (21 / 16 : ℝ) + 1 / 48 = 4 / 3 := by norm_num
  rw [he] at habs
  have hN : (dyadicScale k : ℝ) ^ (21 / 16 : ℝ) =
      (6 : ℝ) ^ (21 / 16 : ℝ) * (scale k : ℝ) ^ (21 / 16 : ℝ) := by
    rw [dyadicScale, Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
  have hsmall : A * (dyadicScale k : ℝ) ^ (21 / 16 : ℝ) ≤
      (scale k : ℝ) ^ (4 / 3 : ℝ) / 16 := by
    rw [hN]
    nlinarith only [habs]
  obtain ⟨hwidth, hlarge⟩ := hw k hkw
  refine ⟨k, hk, hk2, ?_⟩
  intro H hH
  rw [show (31 / 24 : ℝ) + 1 / 48 = 21 / 16 by norm_num]
  exact (hsmall.trans_lt (by linarith only [hp])).trans_le
    (total_lower_four_thirds hH k hk2 hwidth hlarge)

theorem no_uniform_radius_one_bound (D : ℕ) (hD : 1 ≤ D) :
    ¬ ∃ A : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ 3 →
      profile N L (D * (L + 1)) ≤
        A * (N : ℝ) ^ ((31 / 24 : ℝ) + 1 / 48) := by
  rintro ⟨A, N₀, hA⟩
  obtain ⟨k, hk, hk2, hbad⟩ := violates_printed_exponent A N₀
  have hN : N₀ ≤ dyadicScale k := by
    have hi := index_le_scale k
    have hp := scale_pos k
    dsimp [dyadicScale]
    omega
  have hupper := hA (dyadicScale k) hN (3 * k) (critical_band k)
  change total (dyadicScale k) (D * width k) k ≤ _ at hupper
  have hH : 3 ≤ D * width k := by
    have hh : width k ≤ D * width k := by simpa only [one_mul] using Nat.mul_le_mul_right (width k) hD
    dsimp [width] at hh ⊢
    omega
  exact (not_lt_of_ge hupper) (hbad _ hH)

end PaperP1.AsymmetricAlignmentScopeObstruction
