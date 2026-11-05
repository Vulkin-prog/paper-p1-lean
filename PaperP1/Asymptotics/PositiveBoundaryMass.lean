module

public import PaperP1.Asymptotics.RetainedComponentActivity
public import PaperP1.Asymptotics.RetainedIndependentDeficitRates
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Model.RegularMomentTransfer

/-! # Companion T17.3: the exact finite boundary inequality and its uniform four-fifths rate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveBoundaryMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RetainedBoundaryPositiveMass
  PaperP1.RetainedComponentActivity

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ K : ℕ, 4 * K ≤ L →
        mass (8 * (L + 1) : ℕ) N L K ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  let δ := min (ε / 4) (1 / 12)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδcap : δ ≤ 1 / 12 := min_le_right _ _
  obtain ⟨NC, _hNC, hc⟩ := uniform_bounds C δ hδ
  obtain ⟨ND, _hND, hd⟩ := RetainedIndependentDeficitRates.uniform_strong C (ε / 2) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NX, hx⟩ := HalfCountSchedule.factor_absorption 2 (-7 / 12) (1 / 12) (by norm_num)
  let M : ℝ := 2 * (2 : ℝ) ^ C
  let A : ℝ := 2 + Real.exp (2 * M) * (2 + 2 * Real.exp 1)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption A (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + ND + NM + NG + NX + NF + NC, by omega, ?_⟩
  intro N hN L hband K hK
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  let H : ℝ := (8 * (L + 1) : ℕ)
  let a := goodActivity H N L
  let b := badActivity H N L
  let c := higherActivity N L K
  let x := a + b + c
  let P := (N : ℝ) ^ (-4 / 5 + ε / 2)
  have hP : 0 ≤ P := Real.rpow_nonneg hn.le _
  obtain ⟨ha, hb, hc0⟩ := activities_nonneg H N L K hL
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  change 0 ≤ c at hc0
  have hx0 : 0 ≤ x := add_nonneg (add_nonneg ha hb) hc0
  obtain ⟨hbad, hhigh, hpair⟩ := hc N (by omega) L hband K hK
  change b ≤ (N : ℝ) ^ (-4 / 5 + δ) at hbad
  change c ≤ (N : ℝ) ^ (-1 + δ) at hhigh
  change a + b ≤ (N : ℝ) ^ (-2 / 3 + δ) at hpair
  have hbP : b ≤ P := hbad.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδε, hε]))
  have hcP : c ≤ P := hhigh.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδε, hε]))
  have hxcap : x ≤ 2 * (N : ℝ) ^ (-7 / 12 : ℝ) := by
    have hp : a + b ≤ (N : ℝ) ^ (-7 / 12 : ℝ) := hpair.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδcap]))
    have hc : c ≤ (N : ℝ) ^ (-7 / 12 : ℝ) := hhigh.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδcap]))
    change a + b + c ≤ _
    linarith only [hp, hc]
  have hx1 : x ≤ 1 := by
    have hfactor := hx N (by omega)
    have hpower : (N : ℝ) ^ ((-7 / 12 : ℝ) + 1 / 12) ≤ 1 :=
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-7 / 12 : ℝ) + 1 / 12 ≤ 0)).trans_eq (Real.rpow_zero N)
    exact hxcap.trans (hfactor.trans hpower)
  have hsq : x ^ 2 ≤ 4 * P := by
    have h := pow_le_pow_left₀ hx0 hxcap 2
    have hid : ((N : ℝ) ^ (-7 / 12 : ℝ)) ^ 2 = (N : ℝ) ^ (-7 / 6 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
      congr 1
      norm_num
    rw [mul_pow, hid] at h
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])) (by norm_num))
  have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
  have hTaylor : Real.exp x - 1 - a ≤ b + c + (x ^ 2 / 2) * Real.exp x := by
    simpa only [x, add_assoc] using FinitePolymerRemainder.exponential_error a (b + c) ha (add_nonneg hb hc0)
  have hquadratic : (x ^ 2 / 2) * Real.exp x ≤ (2 * Real.exp 1) * P := by
    have hmul := mul_le_mul (div_le_div_of_nonneg_right hsq (by norm_num)) hexp
      (Real.exp_nonneg x) (by positivity : 0 ≤ (4 * P) / 2)
    exact hmul.trans_eq (by ring)
  have herror : Real.exp x - 1 - a ≤ (2 + 2 * Real.exp 1) * P := by
    linarith only [hTaylor, hbP, hcP, hquadratic]
  have hmean : CountObservables.countMoment (RegularStarts.regularStarts N L) L 1 ≤ M :=
    (RegularMomentTransfer.countMoment_mono (Subset.refl (dyadicBlock N)) (RegularStarts.regularStarts_subset N L) 1).trans
      (hm N (by omega) L hband).2
  have hfree : Real.exp (2 * CountObservables.countMoment (RegularStarts.regularStarts N L) L 1) ≤ Real.exp (2 * M) :=
    Real.exp_le_exp.mpr (by linarith only [hmean])
  obtain ⟨hfirst, hsecond⟩ := hd N (by omega) L hband H
  have hfirstP := hfirst.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [] : (-1 : ℝ) + ε / 2 ≤ -4 / 5 + ε / 2))
  have hsecondP := hsecond.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [] : (-7 / 6 : ℝ) + ε / 2 ≤ -4 / 5 + ε / 2))
  change RetainedReferenceTheorem.firstMass N L ≤ P at hfirstP
  change RetainedReferenceTheorem.secondMass H N L ≤ P at hsecondP
  have hfinite := RetainedBoundaryPositiveMass.finite_bound H N L K (by omega) hL
  have hprod := (mul_le_mul_of_nonneg_left herror
    (Real.exp_nonneg (2 * CountObservables.countMoment (RegularStarts.regularStarts N L) L 1))).trans
    (mul_le_mul_of_nonneg_right hfree (by positivity : 0 ≤ (2 + 2 * Real.exp 1) * P))
  have hbudget : mass H N L K ≤ A * P := by
    change mass H N L K ≤ RetainedReferenceTheorem.firstMass N L + RetainedReferenceTheorem.secondMass H N L +
      Real.exp (2 * CountObservables.countMoment (RegularStarts.regularStarts N L) L 1) * (Real.exp x - 1 - a) at hfinite
    dsimp only [A]
    linarith only [hfinite, hfirstP, hsecondP, hprod]
  calc
    _ ≤ A * P := hbudget
    _ ≤ (N : ℝ) ^ ((-4 / 5 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem companion_T17_3 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ K : ℕ, 4 * K ≤ L →
        mass (8 * (L + 1) : ℕ) N L K ≤ RetainedReferenceTheorem.firstMass N L + RetainedReferenceTheorem.secondMass (8 * (L + 1) : ℕ) N L +
          Real.exp (2 * CountObservables.countMoment (RegularStarts.regularStarts N L) L 1) *
            (Real.exp (goodActivity (8 * (L + 1) : ℕ) N L + badActivity (8 * (L + 1) : ℕ) N L + higherActivity N L K) -
              1 - goodActivity (8 * (L + 1) : ℕ) N L) ∧
        mass (8 * (L + 1) : ℕ) N L K ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨N₀, _hN₀, h⟩ := uniform_bound C ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨10 + N₀ + NG, by omega, ?_⟩
  intro N hN L hband K hK
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  exact ⟨RetainedBoundaryPositiveMass.finite_bound _ N L K (by omega) hL,
    h N (by omega) L hband K hK⟩

end PaperP1.PositiveBoundaryMass
