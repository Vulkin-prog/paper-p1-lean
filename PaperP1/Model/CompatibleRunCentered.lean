module

public import PaperP1.Affine.FamilyCenteredMass
public import PaperP1.Model.CanonicalRunComponents
public import PaperP1.Model.SquareClassRelations
public import PaperP1.Model.MissingBlockProbabilities

/-! # Compatible original run families have nonnegative centered coefficients at every order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompatibleRunCentered

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.UniformFubini PaperP1.Probability

local instance compatibleRunCenteredTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance compatibleRunCenteredMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance compatibleRunCenteredDecEq (α : Type*) : DecidableEq α := Classical.decEq α

variable {ι : Type*} [Fintype ι]

theorem finite_centered_eq (M L : ℕ) (g : ι → ℕ) (hL : 0 < L) :
    startFamilyCenteredMoment M L g =
      FamilyCenteredMass.centered (fun i ↦ startSystem M (g i) L) (fun _ ↦ startRhs L) := by
  classical
  unfold startFamilyCenteredMoment FamilyCenteredMass.centered
  apply UniformFubini.congr
  intro ω
  apply prod_congr rfl
  intro i _
  rw [exactMarginal_start_eq_affineMass M (g i) L hL]
  congr 1
  have hevent := startSystem_eq_startRhs_iff (M := M) (x := g i) ω hL
  by_cases h : startSystem M (g i) L ω = startRhs L
  · simp [indicatorValue, startIndicator, h, hevent.mp h]
  · simp [indicatorValue, startIndicator, h, mt hevent.mpr h]

theorem row_count (M L : ℕ) (g : ι → ℕ) (hL : 0 < L) (hcut : ∀ i, g i + L ≤ M)
    (hq : 0 < infiniteFamilyJointMoment L g) :
    infiniteFamilyCenteredMoment L g = (∏ i, infiniteMarginal (g i) L) *
      (Nat.card {s : (i : ι) → startFamilySpace M L g i //
        IsFullSupportRelation (startFamilySpace M L g) s} : ℝ) := by
  classical
  have hfinite : 0 < startFamilyJointMoment M L g := by
    rwa [← infiniteFamilyJointMoment_eq_finite M L g hcut]
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp ((startFamilyJointMoment_pos_iff M L g hL).mp hfinite)
  have hlocal (i : ι) : startSystem M (g i) L a = startRhs L := by
    funext j
    exact congrFun ha (i, j)
  have hmarginal (i : ι) : uniformSolutionMass (startSystem M (g i) L) (startRhs L) = infiniteMarginal (g i) L := by
    rw [infiniteMarginal_eq_finite (hcut i), exactMarginal_start_eq_affineMass M (g i) L hL]
  calc
    _ = startFamilyCenteredMoment M L g := infiniteFamilyCenteredMoment_eq_finite M L g hcut
    _ = FamilyCenteredMass.centered (fun i ↦ startSystem M (g i) L) (fun _ ↦ startRhs L) :=
      finite_centered_eq M L g hL
    _ = (∏ i, uniformSolutionMass (startSystem M (g i) L) (startRhs L)) *
        (Nat.card {s : (i : ι) → startFamilySpace M L g i //
        IsFullSupportRelation (startFamilySpace M L g) s} : ℝ) :=
      FamilyCenteredMass.of_witness_cardinality (fun i ↦ startSystem M (g i) L) (fun _ ↦ startRhs L) a hlocal
    _ = _ := by simp_rw [hmarginal]

theorem full_support_count_eq (M L : ℕ) (g : ι → ℕ) (hcut : ∀ i, g i + L ≤ M) :
    Nat.card {s : (i : ι) → squareClassFamilySpace L g i //
      IsFullSupportRelation (squareClassFamilySpace L g) s} =
    Nat.card {s : (i : ι) → startFamilySpace M L g i //
      IsFullSupportRelation (startFamilySpace M L g) s} := by
  classical
  let e := squareClassFamilyEquivRow M L g hcut
  apply Nat.card_congr
  exact {
    toFun := fun s ↦ ⟨e s.val, (squareClassFamily_full_relation_iff M L g hcut s.val).mpr s.property⟩
    invFun := fun t ↦ ⟨e.symm t.val, (squareClassFamily_full_relation_iff M L g hcut (e.symm t.val)).mp
      (by simpa only [e, LinearEquiv.apply_symm_apply] using t.property)⟩
    left_inv := fun s ↦ Subtype.ext (e.symm_apply_apply s.val)
    right_inv := fun t ↦ Subtype.ext (e.apply_symm_apply t.val) }

theorem square_class_count (L : ℕ) (g : ι → ℕ) (hL : 0 < L) (hq : 0 < infiniteFamilyJointMoment L g) :
    infiniteFamilyCenteredMoment L g = (∏ i, infiniteMarginal (g i) L) *
      (Nat.card {s : (i : ι) → squareClassFamilySpace L g i //
        IsFullSupportRelation (squareClassFamilySpace L g) s} : ℝ) := by
  let M := univ.sup fun i ↦ g i + L
  have hcut : ∀ i, g i + L ≤ M := fun i ↦ le_sup (f := fun i ↦ g i + L) (mem_univ i)
  rw [row_count M L g hL hcut hq, full_support_count_eq M L g hcut]

theorem nonneg (L : ℕ) (g : ι → ℕ) (hL : 0 < L) (hq : 0 < infiniteFamilyJointMoment L g) :
    0 ≤ infiniteFamilyCenteredMoment L g := by
  rw [square_class_count L g hL hq]
  exact mul_nonneg (prod_nonneg (fun i _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg (g i) L))
    (Nat.cast_nonneg _)

theorem coefficient_nonneg (L : ℕ) (I : Finset ℕ) (hL : 0 < L) (hq : 0 < infiniteJointMoment L I) :
    0 ≤ infiniteCenteredCoefficient L I := by
  classical
  rw [infiniteCenteredCoefficient_eq_family_subtype]
  rw [infiniteJointMoment_eq_family_subtype] at hq
  exact nonneg L _ hL hq

end PaperP1.CompatibleRunCentered
