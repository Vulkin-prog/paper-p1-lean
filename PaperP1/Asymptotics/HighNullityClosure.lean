module

public import PaperP1.Model.HighNullityCoreCover
public import PaperP1.Asymptotics.AllCardinalityCoreMass

/-! # Entire high compatible-nullity activity on the literal linear cardinality range has exponent1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HighNullityClosure

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
 

theorem uniform_bound (t : ℕ) (η u C ε : ℝ) (htEven : Even t) (ht : 2 ≤ t)
    (hη : 0 ≤ η) (htη : η + 2 ≤ t) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ K : ℕ, 2 * (t - 2) * K ≤ L →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ I.card ≤ K ∧ (L : ℝ) < runCompatibleNullity L I ∧
          (runCompatibleNullity L I : ℝ) ≤ η * L) →
        (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε) := by
  let v := (2 : ℝ) ^ (t - 2 + 1) * u
  let M := v * (2 * (2 : ℝ) ^ C)
  have hv : 0 < v := by dsimp [v]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨NC, _hNC, hc⟩ := AllCardinalityCoreMass.uniform_bound t η v C (ε / 2)
    htEven ht hη htη hv (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (Real.exp M) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NM + NG + NF + NC, by omega, ?_⟩
  intro N hN L hband K hK G hG F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hcard : (G.card : ℝ) ≤ N := by
    have h := card_le_card hG
    rw [dyadicBlock_card] at h
    exact_mod_cast h
  have hcap (x : ℕ) (hx : x ∈ G) : v * infiniteMarginal x L ≤ M / N := by
    have h := mul_le_mul_of_nonneg_left (hm N (by omega) L hband x (hG hx)) hv.le
    simpa only [M, mul_div_assoc] using h
  have hmean : (∑ x ∈ G, v * infiniteMarginal x L) ≤ M := by
    calc
      _ ≤ ∑ _x ∈ G, M / N := sum_le_sum hcap
      _ = (G.card : ℝ) * (M / N) := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (M / N) := mul_le_mul_of_nonneg_right hcard (div_nonneg hM hn.le)
      _ = M := by field_simp
  have hsource : (∑ D ∈ HighNullityCoreCover.cores G t L η, v ^ D.card * infiniteJointMoment L D) ≤
      (N : ℝ) ^ (-1 + ε / 2) := by
    apply hc N (by omega) L hband G hG (HighNullityCoreCover.cores G t L η)
    intro D hD
    obtain ⟨hDG, hcore, _hq, hhigh, hcapD⟩ := (HighNullityCoreCover.mem_cores G D t L η).mp hD
    exact ⟨hDG, hcore, hhigh, hcapD⟩
  have hnonneg : 0 ≤ ∑ D ∈ HighNullityCoreCover.cores G t L η, v ^ D.card * infiniteJointMoment L D :=
    sum_nonneg fun D _ ↦ mul_nonneg (pow_nonneg hv.le _) (infiniteJointMoment_nonneg L D)
  calc
    _ ≤ Real.exp (∑ x ∈ G, v * infiniteMarginal x L) *
        ∑ D ∈ HighNullityCoreCover.cores G t L η, v ^ D.card * infiniteJointMoment L D :=
      HighNullityCoreCover.finite_bound G t L K η u ht hL hK hu.le F hF
    _ ≤ Real.exp M * ∑ D ∈ HighNullityCoreCover.cores G t L η, v ^ D.card * infiniteJointMoment L D :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmean) hnonneg
    _ ≤ Real.exp M * (N : ℝ) ^ (-1 + ε / 2) :=
      mul_le_mul_of_nonneg_left hsource (Real.exp_nonneg _)
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.HighNullityClosure
