module

public import PaperP1.Asymptotics.LateOriginalCore
public import PaperP1.Asymptotics.PrimeCylinderLiminf

/-! # Companion T19.9: one actual family of connected quadratic-nullity components

The chosen family is fixed before every asymptotic tolerance. Its actual
infinite-model joint and centered moments retain their exact definitions.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticComponent

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Affine
  PaperP1.PrimeCylinderScale PaperP1.PrimeCylinderLiminf PaperP1.LateOriginalCore
  PaperP1.LatePrimeRankDensity PaperP1.LatePeelingOrder

def kappa : ℝ := 6 * Real.log 2 / 17

def sizeCoefficient (q : ℕ) : ℝ := (LatePeelingDensity.densityEnvelope q)⁻¹

def nullityCoefficient (q : ℕ) : ℝ := sizeCoefficient q - (((q - 1 : ℕ) : ℝ))⁻¹

def massError (q : ℕ) : ℝ := 2 / Real.sqrt (q - 1 : ℕ)

def selected (q : ℕ) : Finset ℕ := by
  classical
  exact if h : ∃ I, ComponentConclusion q I then Classical.choose h else ∅

theorem selected_spec {q : ℕ} (hq : ∃ I, ComponentConclusion q I) :
    ComponentConclusion q (selected q) := by
  classical
  simp only [selected, dite_eq_left hq]
  exact Classical.choose_spec hq

theorem selected_eventually :
    ∀ᶠ q : ℕ in oddPrimeIndices, ComponentConclusion q (selected q) := by
  rw [oddPrimeIndices, eventually_inf_principal]
  filter_upwards [LateOriginalCore.actual_component] with q hq hprime
  exact selected_spec (hq hprime.1)

theorem length_tendsto : Tendsto (fun q : ℕ ↦ ((q - 1 : ℕ) : ℝ)) atTop atTop := by
  apply (tendsto_natCast_atTop_atTop (R := ℝ)).comp
  refine tendsto_atTop.mpr fun k ↦ eventually_atTop.mpr ⟨k + 1, ?_⟩
  intro q hq
  omega

theorem sizeCoefficient_tendsto : Tendsto sizeCoefficient atTop (nhds kappa) := by
  unfold sizeCoefficient
  simpa only [kappa, densityBound, inv_div] using
    LatePeelingDensity.densityEnvelope_tendsto.inv₀ densityBound_pos.ne'

theorem nullityCoefficient_tendsto : Tendsto nullityCoefficient atTop (nhds kappa) := by
  unfold nullityCoefficient
  have hsmall : Tendsto (fun q : ℕ ↦ (((q - 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_const_nhds.div_atTop length_tendsto :
      Tendsto (fun q : ℕ ↦ (1 : ℝ) / (q - 1 : ℕ)) atTop (nhds 0))
  simpa only [sub_zero] using sizeCoefficient_tendsto.sub hsmall

theorem massError_tendsto : Tendsto massError atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp length_tendsto)

theorem coefficient_bounds {q : ℕ} (hq : 2 ≤ q) {I : Finset ℕ}
    (hI : ComponentConclusion q I) :
    sizeCoefficient q * (q - 1 : ℕ) ≤ I.card ∧
      nullityCoefficient q * (((q - 1 : ℕ) : ℝ)) ^ 2 ≤ runRelativeNullity (q - 1) I := by
  have hL : (((q - 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (show q - 1 ≠ 0 by omega)
  refine ⟨?_, ?_⟩
  · simpa only [sizeCoefficient, div_eq_mul_inv, mul_comm] using hI.2.2.2.2.2.1
  · have heq : nullityCoefficient q * (((q - 1 : ℕ) : ℝ)) ^ 2 =
        (((q - 1 : ℕ) : ℝ)) ^ 2 / LatePeelingDensity.densityEnvelope q - (q - 1 : ℕ) := by
      unfold nullityCoefficient sizeCoefficient
      field_simp
    rw [heq]
    exact hI.2.2.2.2.2.2.1

/-- A literal family form of the source proposition. Both lower-bound
coefficients tend to kappa, and the centered mass has the explicit error
2/sqrt(L). The same family works for every later epsilon tolerance. -/
theorem companion_T19_9 :
    ∃ C : ℕ → Finset ℕ, ∃ a b : ℕ → ℝ,
      Tendsto a atTop (nhds kappa) ∧ Tendsto b atTop (nhds kappa) ∧
      ∀ᶠ q : ℕ in oddPrimeIndices,
        C q ⊆ RegularStarts.regularStarts (size q) (q - 1) ∧ (C q).Nonempty ∧
        canonicalRunPartition (q - 1) (fun i : C q ↦ i.val) = ⊤ ∧
        runCompatibleNullity (q - 1) (C q) = runRelativeNullity (q - 1) (C q) ∧
        a q * (q - 1 : ℕ) ≤ (C q).card ∧
        b q * (((q - 1 : ℕ) : ℝ)) ^ 2 ≤ runRelativeNullity (q - 1) (C q) ∧
        0 < infiniteJointMoment (q - 1) (C q) ∧
        (1 - massError q) * infiniteJointMoment (q - 1) (C q) ≤
          infiniteCenteredCoefficient (q - 1) (C q) ∧
        0 < (1 - massError q) * infiniteJointMoment (q - 1) (C q) ∧
        ∀ (H : ℝ) e, e ∈ GoodEdgeCompression.goodEdges H (size q) (q - 1) → ¬e ⊆ C q := by
  refine ⟨selected, sizeCoefficient, nullityCoefficient, sizeCoefficient_tendsto,
    nullityCoefficient_tendsto, ?_⟩
  have hsmall := massError_tendsto.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hindices : ∀ᶠ q : ℕ in oddPrimeIndices, Nat.Prime q ∧ 2 < q := by
    rw [oddPrimeIndices, eventually_inf_principal]
    exact Eventually.of_forall fun _ hq ↦ hq
  filter_upwards [selected_eventually,
    hsmall.filter_mono (show oddPrimeIndices ≤ atTop from inf_le_left), hindices]
    with q hI hsmallq hq
  obtain ⟨hsize, hrho⟩ := coefficient_bounds (by omega : 2 ≤ q) hI
  obtain ⟨hpop, hne, hconnected, hnull, hpos, _, _, hmass, _, hgood⟩ := hI
  refine ⟨hpop.trans (LatePrimePopulation.population_regular q), hne, hconnected,
    hnull, hsize, hrho, hpos, ?_, mul_pos (by linarith) hpos, hgood⟩
  calc
    _ ≤ (1 - loss q) * infiniteJointMoment (q - 1) (selected q) :=
      mul_le_mul_of_nonneg_right (by
        have h := loss_bound (by omega : 2 ≤ q)
        change loss q ≤ massError q at h
        linarith) hpos.le
    _ ≤ _ := hmass

theorem fixed_family_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in oddPrimeIndices,
      (kappa - ε) * (q - 1 : ℕ) ≤ (selected q).card ∧
      (kappa - ε) * (((q - 1 : ℕ) : ℝ)) ^ 2 ≤ runRelativeNullity (q - 1) (selected q) := by
  have ha := sizeCoefficient_tendsto.eventually
    (eventually_gt_nhds (by linarith : kappa - ε < kappa))
  have hb := nullityCoefficient_tendsto.eventually
    (eventually_gt_nhds (by linarith : kappa - ε < kappa))
  have hq2 : ∀ᶠ q : ℕ in oddPrimeIndices, 2 ≤ q :=
    (eventually_ge_atTop 2).filter_mono (show oddPrimeIndices ≤ atTop from inf_le_left)
  filter_upwards [selected_eventually,
    ha.filter_mono (show oddPrimeIndices ≤ atTop from inf_le_left),
    hb.filter_mono (show oddPrimeIndices ≤ atTop from inf_le_left), hq2] with q hI haq hbq hq
  obtain ⟨hsize, hrho⟩ := coefficient_bounds hq hI
  exact ⟨(mul_le_mul_of_nonneg_right haq.le (Nat.cast_nonneg _)).trans hsize,
    (mul_le_mul_of_nonneg_right hbq.le (sq_nonneg _)).trans hrho⟩

end PaperP1.QuadraticComponent
