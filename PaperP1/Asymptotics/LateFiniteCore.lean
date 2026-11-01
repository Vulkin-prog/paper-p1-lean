module

public import PaperP1.Asymptotics.LatePeelingDensity
public import PaperP1.Probability.PrivateRankPeelingTheorem

/-! # An actual canonical component after peeling the late regular population

All spaces are the original finite-cylinder run-character spaces. The
component is selected from the actual canonical partition of the terminal
subfamily, with its actual centered and joint affine moments.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LateFiniteCore

open Finset Filter PaperP1.Arithmetic PaperP1.Model PaperP1.Affine
  PaperP1.SubspaceFamilyRank PaperP1.PrimeCylinderScale PaperP1.LatePrimePopulation
  PaperP1.LatePrimeRankDensity PaperP1.LatePeelingOrder PaperP1.PrivateCoreMoments

local instance lateFiniteCoreTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

instance spaceFintype (q x : ℕ) : Fintype (spaces q x) := effectiveRowSpaceFintype _

theorem joint_pos (q : ℕ) (σ : SampleSpace (LatePrimeRankDensity.cutoff q)) {B : Finset ℕ} (C : Finset B) :
    0 < componentJoint (spaces q) (fun _ ↦ σ) C := by
  change 0 < effectiveJointMoment (fun i : C ↦ spaces q i.val.val) (fun _ ↦ σ)
  rw [compatible_joint_count]
  apply mul_pos
  · apply prod_pos
    intro i _
    unfold effectiveRate
    have hcard : 0 < Fintype.card (spaces q i.val.val) := Fintype.card_pos_iff.mpr ⟨0⟩
    exact inv_pos.mpr (by exact_mod_cast hcard)
  · positivity

theorem actual_component :
    ∀ᶠ q : ℕ in atTop, ∀ hq : Nat.Prime q,
      ∃ B : Finset ℕ, B ⊆ population q ∧
        ∃ C : (canonicalRelationPartition (fun i : B ↦ spaces q i.val)).parts,
          ((q - 1 : ℕ) : ℝ) / LatePeelingDensity.densityEnvelope q ≤ C.val.card ∧
          ((q - 1 : ℕ) : ℝ) ^ 2 / LatePeelingDensity.densityEnvelope q - (q - 1 : ℕ) ≤
            relativeNullityOn (fun i : B ↦ spaces q i.val) C.val ∧
          0 < componentJoint (spaces q) (fun _ ↦ LatePrimeWindows.sample (size q) q hq) C.val ∧
          (1 - loss q) * componentJoint (spaces q) (fun _ ↦ LatePrimeWindows.sample (size q) q hq) C.val ≤
            componentCentered (spaces q) (fun _ ↦ LatePrimeWindows.sample (size q) q hq) C.val ∧
          0 < componentCentered (spaces q) (fun _ ↦ LatePrimeWindows.sample (size q) q hq) C.val := by
  have hsmall := loss_tendsto_zero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop 2, population_nonempty_eventually,
    order_positive_eventually, LatePeelingDensity.actual_density_envelope, hsmall]
    with q hq2 hpop hord hdensity hsmallq
  intro hq
  let σ : SampleSpace (LatePrimeRankDensity.cutoff q) := LatePrimeWindows.sample (size q) q hq
  let a : ℕ → SampleSpace (LatePrimeRankDensity.cutoff q) := fun _ ↦ σ
  have hcompatible : ∃ b : SampleSpace (LatePrimeRankDensity.cutoff q), ∀ x ∈ population q, effectiveEvent (spaces q x) (a x) b := by
    refine ⟨σ, ?_⟩
    intro x _ s
    rfl
  obtain ⟨B, hBA, _, _, _, hmass, hdense⟩ :=
    PrivateRankPeelingTheorem.companion_T19_8 (spaces q) (population q) a (q - 1) (order q)
      hord (order_le_length q) (fun _ hx ↦ local_rank hx) hcompatible
  have hpositive : 0 < ((population q).card : ℝ) -
      (rank (spaces q) (population q) : ℝ) / (order q : ℝ) := hdensity.1
  obtain ⟨C, _, hsize, hnullity⟩ := hdense hpositive
  have hRpos : 0 < totalRank q := by
    obtain ⟨x, hx⟩ := hpop
    have hlocal := local_rank_le (spaces q) (population q) hx
    rw [local_rank hx] at hlocal
    change q - 1 ≤ totalRank q at hlocal
    omega
  have hDpos : 0 < PrivateRankCore.density (spaces q) (population q) (order q) := by
    exact div_pos (by exact_mod_cast hRpos) hpositive
  have hmonoSize := div_le_div_of_nonneg_left (Nat.cast_nonneg (q - 1)) hDpos hdensity.2
  have hmonoNullity := div_le_div_of_nonneg_left (sq_nonneg (((q - 1 : ℕ) : ℝ))) hDpos hdensity.2
  have hqC : 0 < componentJoint (spaces q) a C.val := joint_pos q σ C.val
  have hmassC := hmass C
  have hmassGlobal : (1 - loss q) * componentJoint (spaces q) a C.val ≤
      componentCentered (spaces q) a C.val := by
    calc
      _ ≤ (1 - (C.val.card : ℝ) * (2 ^ (q - 1) : ℝ)⁻¹ * 2 ^ order q) *
          componentJoint (spaces q) a C.val := by simpa only [loss] using hmassC.2.1
      _ ≤ _ := hmassC.1
  have hcC : 0 < componentCentered (spaces q) a C.val :=
    (mul_pos (by linarith : 0 < 1 - loss q) hqC).trans_le hmassGlobal
  refine ⟨B, hBA, C, hmonoSize.trans hsize, ?_, hqC, hmassGlobal, hcC⟩
  exact (sub_le_sub_right hmonoNullity (((q - 1 : ℕ) : ℝ))).trans hnullity

end PaperP1.LateFiniteCore
