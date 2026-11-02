module

public import PaperP1.Model.HomogeneousRunMass
public import PaperP1.Asymptotics.UnorderedSeedMassPropagation
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Fixed unordered extensions propagate actual homogeneous and regular rank mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSeedPropagation

open Finset PaperP1.Model PaperP1.RunFamilyEnumeration PaperP1.HomogeneousRunMass
  PaperP1.PrimitiveNominalMass

theorem sum_tuples {r L : ℕ} (F : Finset (Finset ℕ)) (hF : ∀ I ∈ F, I.card = r) :
    (∑ x ∈ tuples F r, PrescribedTupleMass.joint L (fun _ ↦ 0) x) =
      ∑ I ∈ F, probability L I := by
  classical
  unfold tuples
  rw [sum_image]
  · exact sum_congr rfl (fun I hI ↦ by rw [tuple_probability, canonical_values (hF I hI)])
  · intro I hI J hJ hh
    have hv := congrArg FiniteFamilyEnumeration.tupleSet hh
    simpa only [canonical_values (hF I hI), canonical_values (hF J hJ)] using hv

theorem uniform_probability_mass (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (Finset ℕ), (∀ D ∈ F, D ⊆ dyadicBlock N ∧ D.card = s) →
      ∀ T : Finset (Finset ℕ),
        (∀ I ∈ T, I ⊆ dyadicBlock N ∧ I.card = s + k ∧ ∃ D ∈ F, D ⊆ I) →
        (∑ I ∈ T, probability L I) ≤
          ((s + k).factorial : ℝ) * (N : ℝ) ^ ε * ∑ D ∈ F, probability L D := by
  classical
  obtain ⟨N₀, hN₀⟩ := PositionedMassPropagation.all_positions s hs k C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband F hF T hT
  have hsub : tuples T (s + k) ⊆ TuplePositions.allPositions (dyadicBlock N) (tuples F s) k := by
    intro x hx
    obtain ⟨I, hI, rfl⟩ := mem_image.mp hx
    obtain ⟨D, hD, hDI⟩ := (hT I hI).2.2
    exact seeded_tuple_mem (dyadicBlock N) F hF I (hT I hI).1 (hT I hI).2.1 hD hDI
  rw [← sum_tuples T (fun I hI ↦ (hT I hI).2.1), ← sum_tuples F (fun D hD ↦ (hF D hD).2)]
  exact (sum_le_sum_of_subset_of_nonneg hsub
    (fun x _ _ ↦ PrescribedTupleMass.joint_nonneg (fun _ ↦ 0) x)).trans
      (hN₀ N hN L hband (fun _ ↦ 0) (tuples F s)
        (tuples_coordinates (dyadicBlock N) F hF))

theorem uniform_nominal_mass (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (Finset ℕ), (∀ D ∈ F, D ⊆ RegularStarts.regularStarts N L ∧ D.card = s) →
      ∀ T : Finset (Finset ℕ),
        (∀ I ∈ T, I ⊆ RegularStarts.regularStarts N L ∧ I.card = s + k ∧ ∃ D ∈ F, D ⊆ I) →
        mass T L ≤ ((s + k).factorial : ℝ) * (N : ℝ) ^ ε * mass F L := by
  obtain ⟨N₀, hN₀⟩ := uniform_probability_mass s hs k C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband F hF T hT
  have hraw := hN₀ N hN L hband F
    (fun D hD ↦ ⟨(hF D hD).1.trans (RegularStarts.regularStarts_subset N L), (hF D hD).2⟩) T
    (fun I hI ↦ ⟨(hT I hI).1.trans (RegularStarts.regularStarts_subset N L), (hT I hI).2⟩)
  have hf : (∑ D ∈ F, probability L D) = mass F L :=
    sum_congr rfl (fun D hD ↦ regular_weight (hF D hD).1)
  have ht : (∑ I ∈ T, probability L I) = mass T L :=
    sum_congr rfl (fun I hI ↦ regular_weight (hT I hI).1)
  rw [hf, ht] at hraw
  exact hraw

theorem uniform_regular_mass (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ,
      G ⊆ RegularStarts.regularStarts N L → mass (G.powersetCard r) L ≤ (N : ℝ) ^ ε := by
  classical
  by_cases hr : r = 0
  · subst r
    refine ⟨2, le_rfl, ?_⟩
    intro N hN L _ G _
    simpa only [mass, powersetCard_zero, sum_singleton, nominal_empty] using
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) hε.le
  · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr
    obtain ⟨NP, hp⟩ := uniform_nominal_mass 1 (by omega) (r - 1) C (ε / 2) (by positivity)
    obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((r.factorial : ℝ) * (2 : ℝ) ^ C)
      (ε / 2) (ε / 2) (by positivity)
    refine ⟨max 2 (max NP NF), by omega, ?_⟩
    intro N hN L hband G hG
    have hGD := hG.trans (RegularStarts.regularStarts_subset N L)
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hcard : (G.card : ℝ) ≤ N := by
      exact_mod_cast (card_le_card hGD).trans_eq (dyadicBlock_card N)
    have hsource : mass (G.powersetCard 1) L ≤ (2 : ℝ) ^ C := by
      unfold mass
      rw [SubsetSums.one]
      simp_rw [nominal_singleton]
      rw [sum_const, nsmul_eq_mul]
      calc
        _ ≤ (N : ℝ) * (2 ^ L : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ ≤ (N : ℝ) * ((2 : ℝ) ^ C / N) :=
          mul_le_mul_of_nonneg_left (LocalRigidityConsequences.nominal_marginal_bound (by omega) hband) hn.le
        _ = _ := by field_simp
    have hseeds : ∀ D ∈ G.powersetCard 1, D ⊆ RegularStarts.regularStarts N L ∧ D.card = 1 := by
      intro D hD
      obtain ⟨hDG, hcardD⟩ := mem_powersetCard.mp hD
      exact ⟨hDG.trans hG, hcardD⟩
    have htargets : ∀ I ∈ G.powersetCard r, I ⊆ RegularStarts.regularStarts N L ∧
        I.card = 1 + (r - 1) ∧ ∃ D ∈ G.powersetCard 1, D ⊆ I := by
      intro I hI
      obtain ⟨hIG, hcardI⟩ := mem_powersetCard.mp hI
      obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < I.card)
      exact ⟨hIG.trans hG, by omega, {x},
        mem_powersetCard.mpr ⟨singleton_subset_iff.mpr (hIG hx), by simp⟩,
        singleton_subset_iff.mpr hx⟩
    have hraw := hp N (by omega) L hband (G.powersetCard 1) hseeds (G.powersetCard r) htargets
    rw [show 1 + (r - 1) = r by omega] at hraw
    calc
      _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ (ε / 2) * mass (G.powersetCard 1) L := hraw
      _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ (ε / 2) * (2 : ℝ) ^ C :=
        mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = ((r.factorial : ℝ) * (2 : ℝ) ^ C) * (N : ℝ) ^ (ε / 2) := by ring
      _ ≤ (N : ℝ) ^ (ε / 2 + ε / 2) := hf N (by omega)
      _ = _ := by congr 1; ring

end PaperP1.HomogeneousSeedPropagation
