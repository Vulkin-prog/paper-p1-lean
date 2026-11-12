module

public import PaperP1.Model.PrimitiveOrderedMass
public import PaperP1.Asymptotics.FixedArityHomogeneousMass

/-! # V2 companion T4.7: the strong four-weight bound on ordered regular lists

Enumeration costs at most r! and the arity is fixed before the scale threshold.
Homogeneous mass controls the nominal regular weight, actual joint probability
and absolute centered coefficient separately, without an affine sign argument.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.SharpOrderedPrimitiveMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies PaperP1.FiniteFamilyEnumeration

theorem finite_ordered_bound (N L r : ℕ) (w : Finset ℕ → ℝ) (hw : ∀ I, 0 ≤ w I) :
    (∑ n ∈ PrimitiveOrderedMass.lists N L r, w (tupleSet n)) ≤
      (r.factorial : ℝ) * ∑ I ∈ primitiveFamilies (RegularStarts.regularStarts N L) L r, w I := by
  classical
  apply FamilyEnumerationWeights.weighted_bound _ _ w hw
    (fun I hI ↦ (mem_powersetCard.mp (mem_filter.mp hI).1).2)
  intro n hn
  obtain ⟨_, hinj, hprim, _⟩ := (PrimitiveOrderedMass.mem_lists N L r n).mp hn
  exact ⟨hinj, mem_filter.mpr ⟨mem_powersetCard.mpr
    ⟨PrimitiveOrderedMass.tuple_regular hn, FamilyEnumerationUpper.tupleSet_card n hinj⟩, hprim⟩⟩

theorem uniform_homogeneous_mass (r : ℕ) (hr : 3 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ n ∈ PrimitiveOrderedMass.lists N L r, HomogeneousRunMass.probability L (tupleSet n)) ≤
        (N : ℝ) ^ (-(r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NM, _hNM, hm⟩ := FixedArityHomogeneousMass.uniform_mass r hr C (ε / 2) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (r.factorial : ℝ)
    (-(r : ℝ) / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NM + NA, by omega, ?_⟩
  intro N hN L hband
  have hb := hm N (by omega) L hband (primitiveFamilies (RegularStarts.regularStarts N L) L r) (by
    intro I hI
    obtain ⟨hIG, hprim⟩ := mem_filter.mp hI
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hIG
    exact ⟨hsub.trans (RegularStarts.regularStarts_subset N L), hcard, hprim⟩)
  calc
    _ ≤ (r.factorial : ℝ) * ∑ I ∈ primitiveFamilies (RegularStarts.regularStarts N L) L r,
        HomogeneousRunMass.probability L I :=
      finite_ordered_bound N L r _ (fun I ↦ (HomogeneousRunMass.probability_pos L I).le)
    _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ (-(r : ℝ) / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ ≤ (N : ℝ) ^ ((-(r : ℝ) / 2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem companion_T4_7 (r : ℕ) (hr : 3 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      PrimitiveOrderedMass.mass N L r ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε) ∧
      (∑ n ∈ PrimitiveOrderedMass.lists N L r, infiniteJointMoment L (tupleSet n)) ≤
        (N : ℝ) ^ (-(r : ℝ) / 2 + ε) ∧
      (∑ n ∈ PrimitiveOrderedMass.lists N L r, |infiniteCenteredCoefficient L (tupleSet n)|) ≤
        (N : ℝ) ^ (-(r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NM, _hNM, hm⟩ := uniform_homogeneous_mass r hr C ε hε
  obtain ⟨NG, _hNG, hg⟩ := FixedArityHomogeneousMass.uniform_nominal_cap C
  refine ⟨10 + NM + NG, by omega, ?_⟩
  intro N hN L hband
  have hL := (hg N (by omega) L hband).1
  have hb := hm N (by omega) L hband
  refine ⟨?_, ?_, ?_⟩
  · apply le_trans _ hb
    apply sum_le_sum
    intro n hn
    rw [← PrimitiveOrderedMass.weight_formula (by omega : 2 ≤ N) hL n hn]
    exact HomogeneousEffectiveWeights.weight_le L hL (tupleSet n)
  · exact (sum_le_sum fun n _ ↦ HomogeneousRunMass.actual_joint_le L hL (tupleSet n)).trans hb
  · apply le_trans _ hb
    apply sum_le_sum
    intro n hn
    have hcard := FamilyEnumerationUpper.tupleSet_card n ((PrimitiveOrderedMass.mem_lists N L r n).mp hn).2.1
    exact HomogeneousEffectiveWeights.centered_le L hL (tupleSet n) (card_pos.mp (by omega))

end PaperP1.SharpOrderedPrimitiveMass
