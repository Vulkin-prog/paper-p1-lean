module

public import PaperP1.Model.LargeCoreFamilyCover
public import PaperP1.Asymptotics.LargeTenCoreMass

/-! # All activities whose chosen compatible core is large have power 3/2 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargeCoreClosureMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.LargeCoreFamilyCover

theorem uniform_bound (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ G ∧ 256 ≤ (PaperP1.ChosenRelationCore.core L I).card ∧
        runCompatibleNullity L I ≤ 2 * L) →
      (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  let v := 512 * u
  let M := v * (2 * (2 : ℝ) ^ C)
  have hv : 0 < v := by dsimp [v]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨NC, _hNC, hc⟩ := PaperP1.LargeTenCoreMass.uniform_actual v C (ε / 2) hv (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := PaperP1.ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NF, hf⟩ := PaperP1.SaturationDegrees.finite_conditions C 12 (by norm_num)
  obtain ⟨NA, ha⟩ := PaperP1.HalfCountSchedule.factor_absorption
    (Real.exp M) (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NC + NM + NF + NA, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB : 2 ≤ L + 1 := (hf N (by omega) L hband).2.1
  have hL : 0 < L := by omega
  have hcard : (G.card : ℝ) ≤ N := by
    have h := card_le_card hG
    rw [dyadicBlock_card] at h
    exact_mod_cast h
  have hcap : ∀ x ∈ G, v * infiniteMarginal x L ≤ M / N := by
    intro x hx
    have h := mul_le_mul_of_nonneg_left (hm N (by omega) L hband x (hG hx)) hv.le
    simpa only [M, mul_div_assoc] using h
  have hmean : (∑ x ∈ G, v * infiniteMarginal x L) ≤ M := by
    calc
      _ ≤ ∑ _x ∈ G, M / N := sum_le_sum (fun x hx ↦ hcap x hx)
      _ = (G.card : ℝ) * (M / N) := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (M / N) := mul_le_mul_of_nonneg_right hcard (div_nonneg hM hn.le)
      _ = M := by field_simp
  have hsource : (∑ D ∈ cores G L, v ^ D.card * infiniteJointMoment L D) ≤
      (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    apply (source_mass_le_actual G L v hv.le).trans
    apply hc N (by omega) L hband (cores G L)
    intro D hD
    obtain ⟨hDG, hsize, hcore, hcapD⟩ := (mem_cores G D L).mp hD
    exact ⟨hDG.trans hG, hsize, hcore, hcapD⟩
  have hsourceNonneg : 0 ≤ ∑ D ∈ cores G L, v ^ D.card * infiniteJointMoment L D :=
    sum_nonneg fun D _ ↦ mul_nonneg (pow_nonneg hv.le _) (infiniteJointMoment_nonneg L D)
  calc
    _ ≤ Real.exp (∑ x ∈ G, v * infiniteMarginal x L) *
        ∑ D ∈ cores G L, v ^ D.card * infiniteJointMoment L D := finite_bound G L hL u hu.le F hF
    _ ≤ Real.exp M * ∑ D ∈ cores G L, v ^ D.card * infiniteJointMoment L D :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmean) hsourceNonneg
    _ ≤ Real.exp M * (N : ℝ) ^ (-3 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_left hsource (Real.exp_nonneg _)
    _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.LargeCoreClosureMass
