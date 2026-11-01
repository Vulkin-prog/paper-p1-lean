module

public import PaperP1.Arithmetic.BadSeedFamilies
public import PaperP1.Asymptotics.PositionedSeedBounds
public import PaperP1.Model.PrescribedRunMass

/-! # Complete fixed-order positive mass of local-defect and contact families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedExceptionalMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.BadSeedFamilies PaperP1.PrescribedTupleMass

theorem defect_bound (r : ℕ) (hr : 1 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ c : ℕ → Fin L → F₂,
        (∑ x ∈ defectFamilies N L r, joint L c x) ≤ K * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  obtain ⟨N₀, hN₀⟩ := PositionedSeedBounds.defects k C ε hε
  refine ⟨(((1 + k).factorial : ℝ) * (2 * (2 : ℝ) ^ C)), by positivity, N₀, ?_⟩
  intro N hN L hL hband c
  exact (sum_le_sum_of_subset_of_nonneg (defect_cover N L k) (fun x _ _ ↦ joint_nonneg c x)).trans
    (hN₀ N hN L hL hband c)

theorem small_order_contacts (N L r : ℕ) (hr : r ≤ 1) : contactFamilies N L r = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨_, _, i, j, hij, _⟩ := (mem_contactFamilies N L r x).mp hx
  have hival := i.isLt
  have hjval := j.isLt
  have heq : i = j := Fin.ext (by omega)
  exact hij heq

theorem contact_bound (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (∑ x ∈ contactFamilies N L r, joint L (fun _ ↦ startRhs L) x) ≤ K * (N : ℝ) ^ (-1 + ε) := by
  by_cases hr : 2 ≤ r
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
    obtain ⟨N₀, hN₀⟩ := PositionedSeedBounds.contacts k C ε hε
    refine ⟨(((2 + k).factorial : ℝ) * ((2 : ℝ) ^ C) ^ 2), by positivity, N₀, ?_⟩
    intro N hN L hL hband
    rw [contact_mass_eq_active]
    exact (sum_le_sum_of_subset_of_nonneg (contact_cover N L k hL)
      (fun x _ _ ↦ joint_nonneg (fun _ ↦ startRhs L) x)).trans (hN₀ N hN L hband (fun _ ↦ startRhs L))
  · refine ⟨1, by norm_num, 0, ?_⟩
    intro N _ L _ _
    rw [small_order_contacts N L r (by omega), sum_empty, one_mul]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _

def badFamilies (N L r : ℕ) := defectFamilies N L r ∪ contactFamilies N L r

theorem bad_mass (r : ℕ) (hr : 1 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (∑ x ∈ badFamilies N L r, joint L (fun _ ↦ startRhs L) x) ≤ K * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨KD, hKD, ND, hND⟩ := defect_bound r hr C ε hε
  obtain ⟨KC, hKC, NC, hNC⟩ := contact_bound r C ε hε
  refine ⟨KD + KC, by linarith, max ND NC, ?_⟩
  intro N hN L hL hband
  have hsum := GraphStarWeights.sum_union_le_nonneg (defectFamilies N L r) (contactFamilies N L r)
    (joint L (fun _ ↦ startRhs L)) (joint_nonneg _)
  calc
    _ ≤ _ := hsum
    _ ≤ KD * (N : ℝ) ^ (-1 + ε) + KC * (N : ℝ) ^ (-1 + ε) :=
      add_le_add (hND N (by omega) L hL hband _) (hNC N (by omega) L hL hband)
    _ = _ := by ring

theorem bad_original_mass (r : ℕ) (hr : 1 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (∑ x ∈ badFamilies N L r, Model.InfiniteStarts.infiniteFamilyJointMoment L x) ≤
          K * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨K, hK, N₀, hN₀⟩ := bad_mass r hr C ε hε
  refine ⟨K, hK, N₀, ?_⟩
  intro N hN L hL hband
  have h := hN₀ N hN L hL hband
  simpa only [PrescribedRunMass.joint_eq_infinite _ hL] using h

end PaperP1.FixedExceptionalMass
