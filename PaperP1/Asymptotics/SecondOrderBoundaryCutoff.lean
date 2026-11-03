module

public import PaperP1.Asymptotics.BoundaryCutoffTrial
public import PaperP1.Model.SecondOrderStoppedLaw
public import PaperP1.Asymptotics.ActualPairRowActivity
public import PaperP1.Asymptotics.LargeBoundaryTail

/-! # A sublogarithmic all-pair cutoff with an unconditional N^-4 large-boundary tail -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondOrderBoundaryCutoff

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts

def cutoff (C : ℝ) (N : ℕ) : ℕ :=
  BoundaryCutoff.cutoff (2 * (2 : ℝ) ^ C) (by positivity) (N ^ 2)

theorem sublogarithmic (C : ℝ) :
    Tendsto (fun N : ℕ ↦ (cutoff C N : ℝ) / Real.log N) atTop (nhds 0) := by
  have hN : Tendsto (fun N : ℕ ↦ N ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have h := (BoundaryCutoffTrial.cutoff_div_log_tendsto (2 * (2 : ℝ) ^ C) (by positivity)).comp hN
  have heq : (fun N : ℕ ↦ (cutoff C N : ℝ) / Real.log N) =
      fun N : ℕ ↦ 2 * ((cutoff C N : ℝ) / Real.log (N ^ 2 : ℕ)) := by
    funext N
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [heq]
  simpa only [Function.comp_def, cutoff, mul_zero] using h.const_mul 2

theorem finite_large_bound {N L : ℕ} (hN : 0 < N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ dyadicBlock N) (P Λ : ℝ) (hP : 0 ≤ P) (hΛ : 0 < Λ)
    (hcap : ∀ x ∈ G, infiniteMarginal x L ≤ P) (hmean : (G.card : ℝ) * P ≤ Λ) :
    SecondOrderStoppedLaw.largeMass G L (BoundaryCutoff.cutoff Λ hΛ (N ^ 2)) ≤
      (2 ^ (2 * L) : ℝ) * ((N ^ 2 : ℕ) : ℝ) ^ (-3 : ℝ) := by
  classical
  let K := BoundaryCutoff.cutoff Λ hΛ (N ^ 2)
  have hsub : SecondOrderStoppedLaw.large G L K ⊆ LargeSubsetWeights.subsets G K := by
    intro I hI
    obtain ⟨hIB, hcard⟩ := mem_filter.mp hI
    exact mem_filter.mpr ⟨(mem_filter.mp hIB).1, hcard⟩
  have htail := BoundaryCutoff.powerset_tail_bound G P Λ hΛ (N ^ 2) (by positivity) hP hmean
  have hmass : SecondOrderStoppedLaw.largeMass G L K ≤
      (2 ^ (2 * L) : ℝ) * LargeSubsetWeights.weightSum G (2 * P) K := by
    rw [SecondOrderStoppedLaw.largeMass, LargeSubsetWeights.weightSum, mul_sum]
    apply (sum_le_sum ?_).trans (sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ ↦ by positivity))
    intro I hI
    obtain ⟨hIB, _hcard⟩ := mem_filter.mp hI
    obtain ⟨hIG, hboundary⟩ := mem_filter.mp hIB
    have hsubI := mem_powerset.mp hIG
    have hρ := (SecondOrderRetainedClass.boundary_nullity hN G I hG hsubI hboundary).2
    have hjoint := PrimitiveWindowMass.joint_le_weight L hL I
    have hprod : (∏ x ∈ I, infiniteMarginal x L) ≤ P ^ I.card := by
      apply (prod_le_prod₀ (fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
        (fun x hx ↦ hcap x (hsubI hx))).trans_eq
      exact prod_const P
    have hpow : (2 ^ runRelativeNullity L I : ℝ) ≤ 2 ^ (2 * L) := pow_le_pow_right₀ (by norm_num) hρ
    have hj : infiniteJointMoment L I ≤ P ^ I.card * (2 ^ (2 * L) : ℝ) :=
      hjoint.trans (mul_le_mul hprod hpow (by positivity) (pow_nonneg hP _))
    have hweighted := mul_le_mul_of_nonneg_left hj (by positivity : (0 : ℝ) ≤ 2 ^ I.card)
    convert hweighted using 1
    rw [mul_pow]
    ring
  exact hmass.trans (mul_le_mul_of_nonneg_left htail (by positivity))

theorem uniform_large_bound (C : ℝ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      SecondOrderStoppedLaw.largeMass G L (cutoff C N) ≤ (2 : ℝ) ^ (2 * C) * (N : ℝ) ^ (-4 : ℝ) := by
  let M := 2 * (2 : ℝ) ^ C
  have hM : 0 < M := by dsimp only [M]; positivity
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨10 + NM + NG, by omega, ?_⟩
  intro N hN L hband G hG
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hcard : G.card ≤ N := (card_le_card hG).trans_eq (RegularSetFinite.card_dyadicBlock N)
  have hmean : (G.card : ℝ) * (M / N) ≤ M := by
    calc
      _ ≤ (N : ℝ) * (M / N) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := by field_simp
  have hfinite := finite_large_bound (by omega : 0 < N) hL G hG (M / N) M (by positivity) hM
    (fun x hx ↦ hm N (by omega) L hband x (hG hx)) hmean
  have hpower : (2 ^ (2 * L) : ℝ) ≤ (2 : ℝ) ^ (2 * C) * (N : ℝ) ^ 2 := by
    have h := LargeBoundaryTail.critical_power_bound 2 (by norm_num) (by omega : 2 ≤ N) hband
    rw [Real.rpow_two] at h
    convert h using 1
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    rfl
  have hsix : ((N ^ 2 : ℕ) : ℝ) ^ (-3 : ℝ) = (N : ℝ) ^ (-6 : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    congr 1
    norm_num
  change SecondOrderStoppedLaw.largeMass G L (cutoff C N) ≤ _ at hfinite
  rw [hsix] at hfinite
  calc
    _ ≤ (2 ^ (2 * L) : ℝ) * (N : ℝ) ^ (-6 : ℝ) := hfinite
    _ ≤ ((2 : ℝ) ^ (2 * C) * (N : ℝ) ^ 2) * (N : ℝ) ^ (-6 : ℝ) :=
      mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hnpos.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hnpos]
      norm_num

end PaperP1.SecondOrderBoundaryCutoff
