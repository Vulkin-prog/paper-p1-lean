module

public import PaperP1.Asymptotics.ProfileStateSteps

/-! # Counting actual square-product tuples inside one fixed dyadic profile -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProfileTupleCount

open Finset PaperP1.EvenPrimePatterns PaperP1.GrowingDegreeProfiles PaperP1.SplitOffsetProducts
open PaperP1.PrescribedPatternDivisors PaperP1.DyadicPatternWeights PaperP1.SplitKernelStates
open PaperP1.FiniteRefinementCount

def mainExponent (v : ℕ) (c : ℝ) : ℝ :=
  (v : ℝ) / 2 + c * ((v : ℝ) * ((v : ℝ) - 1) + 2) * Real.log 2

theorem sum_step_rates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ Fin (Fintype.card ι)) (last : ι) (w : ι → ℝ) (u t : ℝ) :
    (∑ j, if e.symm j = last then t else w (e.symm j) + u) =
      (∑ i ∈ univ.erase last, w i) + ((Fintype.card ι : ℝ) - 1) * u + t := by
  have hv : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨last⟩
  calc
    _ = ∑ i, if i = last then t else w i + u :=
      Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)
    _ = (∑ i ∈ univ.erase last, (w i + u)) + t := by
      have heq := sum_erase_add (univ : Finset ι) (fun i ↦ if i = last then t else w i + u) (mem_univ last)
      rw [ite_eq_left rfl] at heq
      rw [← heq]
      congr 1
      apply sum_congr rfl
      intro i hi
      exact ite_eq_right (mem_erase.mp hi).1
    _ = _ := by
      rw [sum_add_distrib]
      simp only [sum_const, card_erase_of_mem (mem_univ last), card_univ, nsmul_eq_mul,
        Nat.cast_sub hv, Nat.cast_one]

theorem profile_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hv : 2 ≤ Fintype.card ι) (C : ℕ) (hC : 1 ≤ C) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ A : Finset ℤ, ∀ J : Code ι C N A.card,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ∀ T : Finset (ι → ℕ),
      (∀ n ∈ T, (∀ j, N ≤ C * n j ∧ n j ≤ C * N) ∧
        IsSquare (∏ j, kernels A n j) ∧ Valid (kernels A n) J) →
      (T.card : ℝ) ≤ (N : ℝ) ^ (mainExponent (Fintype.card ι) c +
        Real.log (C + 1 : ℕ) / (2 * Real.log N) + ε) := by
  classical
  have hvpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (show 0 < Fintype.card ι by omega)
  let η := ε / Fintype.card ι
  have hη : 0 < η := div_pos hε hvpos
  obtain ⟨Ns, hNs⟩ := PaperP1.ProfileStateSteps.step_count (ι := ι) hv C hC c D A₀ η hc hη
  obtain ⟨Nf, hNf⟩ := PaperP1.ProfileStateSteps.last_step_count (ι := ι) C hC c D A₀ η hc hη
  obtain ⟨Nh, hNh⟩ := PaperP1.SplitTupleExposure.source_height C D A₀
  refine ⟨max 2 (max Ns (max Nf Nh)), ?_⟩
  intro N hN W A J hW heven hcard hwidth hdegree hA T hT
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  by_cases hnon : T.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hnon
    let _ : Nonempty ι := Fintype.card_pos_iff.mp (show 0 < Fintype.card ι by omega)
    have hheight : ∀ j, (kernels A n₀ j : ℝ) ≤ (((C + 1 : ℕ) : ℝ) * N) ^ (A.card : ℝ) := by
      intro j
      have hp := (hNh N (by omega) W (n₀ j) A ((hT n₀ hn₀).1 j).1 ((hT n₀ hn₀).1 j).2 hwidth hA).2
      rw [Real.rpow_natCast]
      exact_mod_cast hp
    obtain ⟨last, e, helast, hcost⟩ := PaperP1.ProfileExposureOrder.exists_profile_equiv
      (kernels A n₀) (kernels_squarefree A n₀) (hT n₀ hn₀).2.1 J (by omega) (hT n₀ hn₀).2.2
      (C + 1 : ℕ) A.card (by positivity) (by exact_mod_cast (show 0 < A.card by omega)) hheight
    let rank := fun i ↦ (e i).val
    have hrank : Function.Injective rank := fun i j hij ↦ e.injective (Fin.ext hij)
    have hlast : ∀ i, rank i ≤ rank last := by
      intro i
      change (e i).val ≤ (e last).val
      rw [helast]
      have hi := (e i).isLt
      omega
    let a : Fin (Fintype.card ι) → ℝ := fun j ↦
      if e.symm j = last then 2 * c * Real.log 2 + η else
        PaperP1.ProfileExposureOrder.cost J A.card rank (e.symm j) + c * Fintype.card ι * Real.log 2 + η
    have hzero : ((T.image (state A rank 0)).card : ℝ) ≤ 1 := by
      have hc0 : (T.image (state A rank 0)).card ≤ 1 := by
        apply card_le_one.mpr
        intro p hp r hr
        obtain ⟨n, _, rfl⟩ := mem_image.mp hp
        obtain ⟨m, _, rfl⟩ := mem_image.mp hr
        exact (PaperP1.PrimePatternStates.state_zero rank n _).trans
          (PaperP1.PrimePatternStates.state_zero rank m _).symm
      exact_mod_cast hc0
    have hstep : ∀ j : Fin (Fintype.card ι),
        ((T.image (state A rank (j.val + 1))).card : ℝ) ≤
          ((T.image (state A rank j.val)).card : ℝ) * (N : ℝ) ^ a j := by
      intro j
      have hj : rank (e.symm j) = j.val := by dsimp [rank]; rw [e.apply_symm_apply]
      by_cases hfinal : e.symm j = last
      · have hki : rank last = j.val := by rw [← hfinal]; exact hj
        have hp := hNf N (by omega) W A rank j.val last hrank hki hlast hW hcard hwidth hdegree hA T
          (fun n hnT ↦ ⟨(hT n hnT).1, (hT n hnT).2.1⟩)
        simpa only [a, ite_eq_left hfinal] using hp
      · have hp := hNs N (by omega) W A J rank j.val (e.symm j) hrank hj
          hW heven hcard hwidth hdegree hA T hT
        simpa only [a, ite_eq_right hfinal] using hp
    have hfinal : Set.InjOn (state A rank (Fintype.card ι)) T := by
      intro n _ m _ hnm
      exact PaperP1.PrimePatternStates.final_coordinate_injective rank (Fintype.card ι)
        (fun i ↦ (e i).isLt) (fun n ↦ part (kernels A n)) hnm
    have hcount := iterate_fin_power_bound T (state A rank) N hn (Fintype.card ι) a hzero hstep hfinal
    have hηeq : (Fintype.card ι : ℝ) * η = ε := by dsimp [η]; field_simp
    have hsum : (∑ j, a j) = (∑ i ∈ univ.erase last, PaperP1.ProfileExposureOrder.cost J A.card rank i) +
        c * ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) + 2) * Real.log 2 + ε := by
      have hs := sum_step_rates e last (fun i ↦ PaperP1.ProfileExposureOrder.cost J A.card rank i)
        (c * Fintype.card ι * Real.log 2 + η) (2 * c * Real.log 2 + η)
      calc
        (∑ j, a j) = (∑ i ∈ univ.erase last, PaperP1.ProfileExposureOrder.cost J A.card rank i) +
            ((Fintype.card ι : ℝ) - 1) * (c * Fintype.card ι * Real.log 2 + η) +
            (2 * c * Real.log 2 + η) := by simpa only [a, add_assoc] using hs
        _ = _ := by nlinarith only [hηeq]
    apply hcount.trans
    apply Real.rpow_le_rpow_of_exponent_le hn1
    rw [hsum]
    unfold mainExponent
    linarith
  · have hempty : T = ∅ := not_nonempty_iff_eq_empty.mp hnon
    rw [hempty, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg hn.le _

end PaperP1.ProfileTupleCount
