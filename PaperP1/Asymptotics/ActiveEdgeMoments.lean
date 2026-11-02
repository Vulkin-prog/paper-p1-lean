module

public import PaperP1.Model.ActiveEdgeObservables
public import PaperP1.Probability.SeededCountMoments
public import PaperP1.Probability.NonnegativeActivation
public import PaperP1.Asymptotics.ActualFamilyJointRows
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # All fixed active-family moments and activation probability relative to actual mass

The deterministic family can be any collection of subsets of one fixed positive cardinality in any
dyadic subground. Zero seed masses, irregular sites and overlaps remain.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActiveEdgeMoments

open Finset MeasureTheory PaperP1.Algebra PaperP1.Arithmetic PaperP1.Probability
  PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.ActiveEdgeObservables

theorem uniform_moment (s : ℕ) (hs : 1 ≤ s) (r : ℕ) (hr : 1 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ F : Finset (Finset ℕ), F ⊆ G.powersetCard s →
      (∫ ω, value F L ω ^ r ∂infiniteRademacherMeasure) ≤
        (N : ℝ) ^ ε * ∑ e ∈ F, infiniteJointMoment L e := by
  let k := s * (r - 1)
  let δ := ε / ((k + 1 : ℕ) : ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NR, _hNR, hrow⟩ := ActualFamilyJointRows.uniform_row (s + k) C δ hδ
  refine ⟨max 2 NR, by omega, ?_⟩
  intro N hN L hband G hG F hF
  let M := dyadicCutoff N L
  let P := cylinderProbability M
  let J : ℕ → SampleSpace M → Bool := fun x ↦ startIndicator x L
  let A := (N : ℝ) ^ δ
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hq (I : Finset ℕ) (hI : I ⊆ G) : finiteJointMoment P J I = infiniteJointMoment L I :=
    (infiniteJointMoment_eq_finite M L I (CountObservables.dyadic_subset_cutoff (hI.trans hG))).symm
  have hfiniteRow (I : Finset ℕ) (hI : I ⊆ G) (hne : I.Nonempty) (hcard : I.card ≤ s + k) :
      (∑ y ∈ G, finiteJointMoment P J (insert y I)) ≤ A * finiteJointMoment P J I := by
    rw [hq I hI]
    calc
      _ = ∑ y ∈ G, infiniteJointMoment L (insert y I) := by
        apply sum_congr rfl
        intro y hy
        exact hq (insert y I) (insert_subset_iff.mpr ⟨hy, hI⟩)
      _ ≤ ∑ y ∈ dyadicBlock N, infiniteJointMoment L (insert y I) :=
        sum_le_sum_of_subset_of_nonneg hG (fun y _ _ ↦ infiniteJointMoment_nonneg L (insert y I))
      _ ≤ _ := hrow N (by omega) L hband I (hI.trans hG) hne hcard
  have hcut : ∀ e ∈ F, ∀ x ∈ e, x + L ≤ M := fun e he x hx ↦
    CountObservables.dyadic_subset_cutoff hG x ((mem_powersetCard.mp (hF he)).1 hx)
  have hqsum : (∑ e ∈ F, finiteJointMoment P J e) = ∑ e ∈ F, infiniteJointMoment L e :=
    sum_congr rfl fun e he ↦ hq e (mem_powersetCard.mp (hF he)).1
  have hbudget : δ * k ≤ ε := by
    have hden : δ * ((k + 1 : ℕ) : ℝ) = ε := by dsimp [δ]; field_simp
    have hk : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    nlinarith only [hden, mul_le_mul_of_nonneg_left hk hδ.le]
  calc
    _ = finiteExpectation P.weight (fun σ ↦ ActivePairCount.value F J σ ^ r) :=
      integral_eq_finite F hcut (fun x ↦ x ^ r)
    _ ≤ A ^ k * ∑ e ∈ F, finiteJointMoment P J e :=
      SeededCountMoments.selected_family_power P J G F s hs hF r hr A (Real.rpow_nonneg hn.le _) hfiniteRow
    _ = (N : ℝ) ^ (δ * k) * ∑ e ∈ F, infiniteJointMoment L e := by
      rw [hqsum]
      dsimp [A]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn1 hbudget)
      (sum_nonneg fun e _ ↦ infiniteJointMoment_nonneg L e)

theorem uniform_activation (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ F : Finset (Finset ℕ), F ⊆ G.powersetCard s →
      (∑ e ∈ F, infiniteJointMoment L e) * (N : ℝ) ^ (-ε) ≤ probability F L ∧
        probability F L ≤ ∑ e ∈ F, infiniteJointMoment L e := by
  obtain ⟨NM, _hNM, hm⟩ := uniform_moment s hs 2 (by decide) C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NM NF), by omega, ?_⟩
  intro N hN L hband G hG F hF
  let M := dyadicCutoff N L
  let P := cylinderProbability M
  let J : ℕ → SampleSpace M → Bool := fun x ↦ startIndicator x L
  let X := ActivePairCount.value F J
  let B := (N : ℝ) ^ (ε / 2)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB : 0 < B := Real.rpow_pos_of_pos hn _
  have hcut : ∀ e ∈ F, ∀ x ∈ e, x + L ≤ M := fun e he x hx ↦
    CountObservables.dyadic_subset_cutoff hG x ((mem_powersetCard.mp (hF he)).1 hx)
  have hsecond : finiteExpectation P.weight (fun σ ↦ X σ ^ 2) ≤ B * finiteExpectation P.weight X := by
    rw [finite_mean_eq F hcut]
    have hmom := hm N (by omega) L hband G hG F hF
    rwa [integral_eq_finite F hcut (fun x ↦ x ^ 2)] at hmom
  have hfinite := NonnegativeActivation.relative_second_bound P X (ActivePairCount.value_nonneg F J) B hB hsecond
  rw [finite_mean_eq F hcut, ← probability_eq_finite F hcut] at hfinite
  have hprob : 0 ≤ probability F L := measureReal_nonneg
  have hfactor : 4 * B ≤ (N : ℝ) ^ ε := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hmass : (∑ e ∈ F, infiniteJointMoment L e) ≤ (N : ℝ) ^ ε * probability F L :=
    hfinite.trans (mul_le_mul_of_nonneg_right hfactor hprob)
  refine ⟨?_, probability_le_mass F hcut⟩
  calc
    _ ≤ ((N : ℝ) ^ ε * probability F L) * (N : ℝ) ^ (-ε) :=
      mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg hn.le _)
    _ = _ := by
      rw [mul_comm ((N : ℝ) ^ ε), mul_assoc, ← Real.rpow_add hn, add_neg_cancel, Real.rpow_zero, mul_one]

end PaperP1.ActiveEdgeMoments
