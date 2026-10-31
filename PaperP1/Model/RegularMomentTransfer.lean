module

public import PaperP1.Model.RegularSetAsymptotic
public import PaperP1.Probability.FiniteMomentTransfer

/-! # Fixed-moment transfer for the regular dyadic count

The higher-moment hypothesis is exactly the conditional premise of main 3.1.
The moment order chosen after j and ε is fixed before N and every band length.
A small coupling error is never used alone to claim a moment estimate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularMomentTransfer

open PaperP1.Arithmetic PaperP1.Model PaperP1.Probability PaperP1.Algebra
open CountObservables RegularStarts RegularSetAsymptotic Finset

theorem countMoment_nonneg {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (j : ℕ) :
    0 ≤ countMoment G L j := by
  rw [countMoment_eq_finite hG]
  exact finiteExpectation_nonneg _ (fun _ ↦ pow_nonneg (Nat.cast_nonneg _) _)

theorem countMoment_mono {N L : ℕ} {G H : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) (hHG : H ⊆ G) (j : ℕ) :
    countMoment H L j ≤ countMoment G L j := by
  rw [countMoment_eq_finite (hHG.trans hG), countMoment_eq_finite hG]
  apply finiteExpectation_mono
  intro ω
  apply pow_le_pow_left₀ (Nat.cast_nonneg _)
  exact_mod_cast indicatorCount_mono hHG _ ω

theorem count_moment_truncation {N L : ℕ} {G H : Finset ℕ}
    (hG : G ⊆ dyadicBlock N) (hHG : H ⊆ G)
    (j q : ℕ) (hjq : j ≤ q) (R : ℝ) (hR : 0 < R) :
    |countMoment G L j - countMoment H L j| ≤
      R ^ j * countDisagreement G H L + countMoment G L q / R ^ (q - j) := by
  rw [countMoment_eq_finite hG, countMoment_eq_finite (hHG.trans hG),
    countDisagreement_eq_finite hG (hHG.trans hG), countMoment_eq_finite hG]
  exact ordered_moment_difference_bound _ _ _ (indicatorCount_mono hHG _) j q hjq R hR

def BoundedCountMomentsOn (C : ℝ) (allowed : ℕ → ℕ → Prop) : Prop :=
  ∀ q : ℕ, 0 < q → ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, allowed N L →
    0 < L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      countMoment (dyadicBlock N) L q ≤ M

def UniformlyBoundedCountMoments (C : ℝ) : Prop :=
  BoundedCountMomentsOn C (fun _ _ ↦ True)

theorem regular_moment_transfer_on (C : ℝ) (allowed : ℕ → ℕ → Prop)
    (hmom : BoundedCountMomentsOn C allowed)
    (j : ℕ) (hj : 0 < j) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, allowed N L → 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |countMoment (dyadicBlock N) L j - countMoment (regularStarts N L) L j| ≤
        K * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨s, hs⟩ := exists_nat_gt (max (0 : ℝ) (2 * (j : ℝ) / ε))
  have hspos : (0 : ℝ) < s := (le_max_left _ _).trans_lt hs
  have hsNat : 0 < s := by exact_mod_cast hspos
  have hsbound : 2 * (j : ℝ) < (s : ℝ) * ε :=
    (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hs)
  let δ : ℝ := (s : ℝ)⁻¹
  have hδj : δ * j ≤ ε / 2 := by
    dsimp [δ]
    have hjdiv : (j : ℝ) / s ≤ ε / 2 := (div_le_iff₀ hspos).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, mul_comm] using hjdiv
  obtain ⟨M, hM, Nmom, hNmom⟩ := hmom (j + s) (by omega)
  obtain ⟨Ncouple, hNcouple⟩ := discarded_activity_critical C (ε / 2) (by positivity)
  let Kc : ℝ := 2 * (2 : ℝ) ^ C
  have hKc : 0 ≤ Kc := by dsimp [Kc]; positivity
  refine ⟨Kc + M, add_nonneg hKc hM, max 2 (max Nmom Ncouple), ?_⟩
  intro N hN L hallowed hL hband
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let R : ℝ := (N : ℝ) ^ δ
  have hR : 0 < R := Real.rpow_pos_of_pos hn _
  have hRj : R ^ j = (N : ℝ) ^ (δ * j) := (Real.rpow_mul_natCast hn.le δ j).symm
  have hRs : R ^ s = (N : ℝ) := by
    rw [← Real.rpow_mul_natCast hn.le δ s]
    have hδs : δ * s = 1 := inv_mul_cancel₀ (ne_of_gt hspos)
    rw [hδs, Real.rpow_one]
  have hqminus : j + s - j = s := by omega
  have htrunc := count_moment_truncation (N := N) (L := L) (subset_refl _)
    (regularStarts_subset N L) j (j + s) (by omega) R hR
  have hcouple := hNcouple N (by omega) L hL hband
  have hm := hNmom N (by omega) L hallowed hL hband
  have hfirst : R ^ j * countDisagreement (dyadicBlock N) (regularStarts N L) L ≤
      Kc * (N : ℝ) ^ (-1 + ε) := by
    calc
      _ ≤ R ^ j * (Kc * (N : ℝ) ^ (-1 + ε / 2)) :=
        mul_le_mul_of_nonneg_left hcouple (pow_nonneg hR.le _)
      _ = Kc * (N : ℝ) ^ (δ * j + (-1 + ε / 2)) := by
        rw [hRj, Real.rpow_add hn (δ * j) (-1 + ε / 2)]
        ac_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)) hKc
  have htail : countMoment (dyadicBlock N) L (j + s) / R ^ (j + s - j) ≤
      M * (N : ℝ) ^ (-1 + ε) := by
    rw [hqminus, hRs]
    calc
      _ ≤ M / N := (div_le_div_iff_of_pos_right hn).mpr hm
      _ = M * (N : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)) hM
  calc
    _ ≤ R ^ j * countDisagreement (dyadicBlock N) (regularStarts N L) L +
        countMoment (dyadicBlock N) L (j + s) / R ^ (j + s - j) := htrunc
    _ ≤ Kc * (N : ℝ) ^ (-1 + ε) + M * (N : ℝ) ^ (-1 + ε) := add_le_add hfirst htail
    _ = _ := by ring

theorem regular_moment_transfer (C : ℝ) (hmom : UniformlyBoundedCountMoments C)
    (j : ℕ) (hj : 0 < j) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |countMoment (dyadicBlock N) L j - countMoment (regularStarts N L) L j| ≤
        K * (N : ℝ) ^ (-1 + ε) := by
  simpa only [true_implies] using regular_moment_transfer_on C (fun _ _ ↦ True) hmom j hj ε hε

/-- A moment bound along one prescribed sequence of lengths suffices;
no uniform bound over other lengths is required. -/
theorem regular_moment_transfer_along (C : ℝ) (length : ℕ → ℕ)
    (hmom : ∀ q : ℕ, 0 < q → ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      0 < length N → |(length N : ℝ) - Real.log N / Real.log 2| ≤ C →
        countMoment (dyadicBlock N) (length N) q ≤ M)
    (j : ℕ) (hj : 0 < j) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < length N →
      |(length N : ℝ) - Real.log N / Real.log 2| ≤ C →
      |countMoment (dyadicBlock N) (length N) j -
        countMoment (regularStarts N (length N)) (length N) j| ≤
          K * (N : ℝ) ^ (-1 + ε) := by
  have hm : BoundedCountMomentsOn C (fun N L ↦ L = length N) := by
    intro q hq
    obtain ⟨M, hM, N₀, hN₀⟩ := hmom q hq
    exact ⟨M, hM, N₀, fun N hN L heq ↦ heq.symm ▸ hN₀ N hN⟩
  obtain ⟨K, hK, N₀, hN₀⟩ := regular_moment_transfer_on C (fun N L ↦ L = length N) hm j hj ε hε
  exact ⟨K, hK, N₀, fun N hN ↦ hN₀ N hN (length N) rfl⟩

end PaperP1.RegularMomentTransfer
