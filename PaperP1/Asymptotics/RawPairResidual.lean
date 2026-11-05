module

public import PaperP1.Asymptotics.PositiveSeparatedSourceProfile

/-! # Positive source mass outside both raw principal channels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawPairResidual

open Finset PaperP1.Model PaperP1.SourcePairPositiveWeight PaperP1.PrincipalPositiveCover
  PaperP1.PrivateChannelPositiveMass

theorem finite_bound {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    2 * (∑ e ∈ separated N L \ principal N H L, setWeight L e) ≤
      |(∑ p ∈ PairSeparation.separatedHosts (dyadicBlock N) L, weight p.1 p.2 L) -
        PositiveSeparatedSourceProfile.mainTerm N L| +
      |channelWeight N H 2 3 L - (N : ℝ) * (ActualSourceTranslations.coefficient 2 3 : ℝ) *
        (ChannelSumIdentity.unsigned L 2 3 : ℤ)| +
      |channelWeight N H 3 4 L - (N : ℝ) * (ActualSourceTranslations.coefficient 3 4 : ℝ) *
        (ChannelSumIdentity.unsigned L 3 4 : ℤ)| := by
  have hpartition := sum_sdiff (f := setWeight L) (principal_subset_separated (H := H) hN hlarge)
  have hprincipal := principal_mass_eq (H := H) hN hlarge
  have hmain : PositiveSeparatedSourceProfile.mainTerm N L =
      (N : ℝ) * (ActualSourceTranslations.coefficient 2 3 : ℝ) * (ChannelSumIdentity.unsigned L 2 3 : ℤ) +
      (N : ℝ) * (ActualSourceTranslations.coefficient 3 4 : ℝ) * (ChannelSumIdentity.unsigned L 3 4 : ℤ) := by
    norm_num [PositiveSeparatedSourceProfile.mainTerm, ActualSourceTranslations.coefficient]
    ring
  let E := (∑ p ∈ PairSeparation.separatedHosts (dyadicBlock N) L, weight p.1 p.2 L) -
    PositiveSeparatedSourceProfile.mainTerm N L
  let F := channelWeight N H 2 3 L - (N : ℝ) * (ActualSourceTranslations.coefficient 2 3 : ℝ) *
    (ChannelSumIdentity.unsigned L 2 3 : ℤ)
  let G := channelWeight N H 3 4 L - (N : ℝ) * (ActualSourceTranslations.coefficient 3 4 : ℝ) *
    (ChannelSumIdentity.unsigned L 3 4 : ℤ)
  have heq : 2 * (∑ e ∈ separated N L \ principal N H L, setWeight L e) = E - F - G := by
    dsimp only [E, F, G]
    rw [hmain, ordered_separated_sum]
    linarith only [hpartition, hprincipal]
  rw [heq]
  change E - F - G ≤ |E| + |F| + |G|
  linarith only [le_abs_self E, neg_le_abs F, neg_le_abs G]

theorem uniform_bound (C ε : ℝ) (D : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
        (∑ e ∈ separated N L \ principal N H L, setWeight L e) ≤ (N : ℝ) ^ (6 / 5 + ε) := by
  obtain ⟨NP, _hNP, hp⟩ :=
    PositiveSeparatedSourceProfile.article_3_3_positive C (ε / 2) (by positivity)
  obtain ⟨N23, _hN23, h23⟩ := PrivateChannelPositiveProfile.uniform_error C (ε / 2) D 2 3
    (by decide) (by decide) (by decide) (by decide) (by positivity)
  obtain ⟨N34, _hN34, h34⟩ := PrivateChannelPositiveProfile.uniform_error C (ε / 2) D 3 4
    (by decide) (by decide) (by decide) (by decide) (by positivity)
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C 29 (by norm_num) 1
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (6 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NP (max N23 (max N34 (max NL NF)))), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlarge : 29 * (L + 1) < N := by
    have h := hl N (by omega) L hband
    simp only [pow_one] at h
    exact_mod_cast h
  have hprofile := hp N (by omega) L hband
  change |(∑ p ∈ PairSeparation.separatedHosts (dyadicBlock N) L, weight p.1 p.2 L) -
    PositiveSeparatedSourceProfile.mainTerm N L| ≤ (N : ℝ) ^ (6 / 5 + ε / 2) at hprofile
  have h23' := h23 N (by omega) L H hband (by omega) hH
  have h34' := h34 N (by omega) L H hband (by omega) hH
  norm_num only [Nat.cast_ofNat] at h23' h34'
  have h23cap := h23'.trans (Real.rpow_le_rpow_of_exponent_le hn1
    (by linarith : 5 / 6 + ε / 2 ≤ 6 / 5 + ε / 2))
  have h34cap := h34'.trans (Real.rpow_le_rpow_of_exponent_le hn1
    (by linarith : 3 / 4 + ε / 2 ≤ 6 / 5 + ε / 2))
  have hfinite := finite_bound (H := H) (by omega : 2 ≤ N) hlarge
  have hpow : 0 ≤ (N : ℝ) ^ (6 / 5 + ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ ≤ 2 * (N : ℝ) ^ (6 / 5 + ε / 2) := by linarith only [hfinite, hprofile, h23cap, h34cap, hpow]
    _ ≤ (N : ℝ) ^ ((6 / 5 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.RawPairResidual
