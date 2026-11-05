module

public import PaperP1.Asymptotics.LowPrimitiveRankMass
public import PaperP1.Model.PrimitiveNominalMass

/-! # Low-nullity primitive homogeneous mass at any fixed size -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LowPrimitiveNominalMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrimitiveNominalMass PaperP1.ConnectedWindowFamilies

theorem uniform_bound (r : ℕ) (hr : 3 ≤ r) (b : ℕ) (hb : 0 < b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = r ∧ Primitive L I ∧
        (runRelativeNullity L I : ℝ) < (L : ℝ) / b) →
      mass F L ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + 1 / (b : ℝ) + ε) := by
  classical
  let K := (2 : ℝ) ^ ((C + 1) / b)
  obtain ⟨NI, hi⟩ := OriginalWindowFamilyMass.article_10_2 r (by omega) C (ε / 2) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (((2 : ℝ) ^ C) ^ r * K)
    (-(r : ℝ) / 2 + 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NI + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsub : F ⊆ primitiveFamilies (dyadicBlock N) L r := by
    intro I hI
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨(hF I hI).1, (hF I hI).2.1⟩, (hF I hI).2.2.1⟩
  have hcount : (F.card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε / 2) := by
    have hc : (F.card : ℝ) ≤ ((primitiveFamilies (dyadicBlock N) L r).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    exact hc.trans (hi N (by omega) L (dyadicBlock N) hband Subset.rfl).2.1
  have hnom := LocalRigidityConsequences.nominal_marginal_bound (by omega : 2 ≤ N) hband
  have hpoint (I : Finset ℕ) (hI : I ∈ F) : weight L I ≤
      (((2 : ℝ) ^ C / N) ^ r) * (K * (N : ℝ) ^ (1 / (b : ℝ))) := by
    have hpow : (2 ^ runRelativeNullity L I : ℝ) ≤ K * (N : ℝ) ^ (1 / (b : ℝ)) := by
      calc
        _ = (2 : ℝ) ^ (runRelativeNullity L I : ℝ) := (Real.rpow_natCast _ _).symm
        _ ≤ (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) ((hF I hI).2.2.2.le.trans
            (div_le_div_of_nonneg_right (by push_cast; linarith) hbR.le))
        _ ≤ _ := CriticalChannelPowers.window_root_upper (by omega) hb hband
    unfold weight
    rw [(hF I hI).2.1]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hnom r) hpow (by positivity) (by positivity)
  have hproduct : (N : ℝ) ^ ((r : ℝ) / 2 + ε / 2) *
      ((((2 : ℝ) ^ C / N) ^ r) * (K * (N : ℝ) ^ (1 / (b : ℝ)))) =
      (((2 : ℝ) ^ C) ^ r * K) * (N : ℝ) ^ (-(r : ℝ) / 2 + 1 / (b : ℝ) + ε / 2) := by
    conv_rhs =>
      rw [show -(r : ℝ) / 2 + 1 / (b : ℝ) + ε / 2 =
        ((r : ℝ) / 2 + ε / 2 + 1 / (b : ℝ)) - r by ring,
        Real.rpow_sub hn, Real.rpow_add hn, Real.rpow_natCast]
    rw [div_pow]
    ring
  calc
    _ ≤ ∑ _I ∈ F, (((2 : ℝ) ^ C / N) ^ r) * (K * (N : ℝ) ^ (1 / (b : ℝ))) := sum_le_sum hpoint
    _ = (F.card : ℝ) * ((((2 : ℝ) ^ C / N) ^ r) * (K * (N : ℝ) ^ (1 / (b : ℝ)))) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε / 2) *
        ((((2 : ℝ) ^ C / N) ^ r) * (K * (N : ℝ) ^ (1 / (b : ℝ)))) :=
      mul_le_mul_of_nonneg_right hcount (by dsimp [K]; positivity)
    _ = (((2 : ℝ) ^ C) ^ r * K) * (N : ℝ) ^ (-(r : ℝ) / 2 + 1 / (b : ℝ) + ε / 2) := hproduct
    _ ≤ (N : ℝ) ^ ((-(r : ℝ) / 2 + 1 / (b : ℝ) + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.LowPrimitiveNominalMass
