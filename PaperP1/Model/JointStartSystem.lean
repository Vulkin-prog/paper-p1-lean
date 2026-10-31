module

public import PaperP1.Model.StartFourier
public import PaperP1.Probability.StoppedFiniteLaw

/-!
# Joint affine system of an arbitrary finite family of run starts

The joint event is an actual intersection, with the same positive length and
left-boundary convention as each individual start. Its effective row space is
the sum of the local effective spaces, including possible incompatibility.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability

namespace PaperP1.Model

local instance jointStartSystemPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance jointStartSystemDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def familyStartSystem (M L : ℕ) (g : ι → ℕ) :
    SampleSpace M →ₗ[F₂] (ι × Fin L → F₂) :=
  LinearMap.pi fun p => startRow M (g p.1) L p.2

def familyStartRhs (L : ℕ) : ι × Fin L → F₂ := fun p => startRhs L p.2

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem familyStartSystem_apply (M L : ℕ) (g : ι → ℕ) (ω : SampleSpace M) (p : ι × Fin L) :
    familyStartSystem M L g ω p = startSystem M (g p.1) L ω p.2 := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem familyStartSystem_eq_iff (M L : ℕ) (g : ι → ℕ) (hL : 0 < L) (ω : SampleSpace M) :
    familyStartSystem M L g ω = familyStartRhs L ↔
      ∀ i, StartEvent (valueBit ω) (g i) L := by
  simp_rw [← startSystem_eq_startRhs_iff ω hL]
  constructor
  · intro h i
    funext j
    exact congrFun h (i, j)
  · intro h
    funext p
    exact congrFun (h p.1) p.2

omit [DecidableEq ι] in
theorem relationMap_familyStartSystem (M L : ℕ) (g : ι → ℕ) (u : ι × Fin L → F₂) :
    relationMap (familyStartSystem M L g) u =
      ∑ i, relationMap (startSystem M (g i) L) (fun j => u (i, j)) := by
  apply LinearMap.ext
  intro ω
  simp only [relationMap_apply, relationFunctional_apply, dotProduct, LinearMap.sum_apply,
    familyStartSystem_apply]
  exact Fintype.sum_prod_type _

theorem effectiveRowSpace_familyStartSystem (M L : ℕ) (g : ι → ℕ) :
    effectiveRowSpace (familyStartSystem M L g) = ⨆ i, startFamilySpace M L g i := by
  apply le_antisymm
  · rintro f ⟨u, rfl⟩
    rw [relationMap_familyStartSystem]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup (startFamilySpace M L g) i) (LinearMap.mem_range_self _ _)
  · refine iSup_le fun i => ?_
    rintro f ⟨u, rfl⟩
    let U : ι × Fin L → F₂ := fun p => if p.1 = i then u p.2 else 0
    refine LinearMap.mem_range.mpr ⟨U, ?_⟩
    rw [relationMap_familyStartSystem, Finset.sum_eq_single i]
    · congr 1
      funext j
      simp [U]
    · intro k _ hki
      have hu : (fun j => U (k, j)) = 0 := by funext j; simp [U, hki]
      rw [hu, map_zero]
    · simp

def startFamilyJointMoment (M L : ℕ) (g : ι → ℕ) : ℝ :=
  finiteExpectation (cylinderProbability M).weight
    (fun ω => ∏ i, (indicatorValue (startIndicator (g i) L ω) : ℝ))

omit [DecidableEq ι] in
theorem startFamilyJointMoment_eq_affineMass (M L : ℕ) (g : ι → ℕ) (hL : 0 < L) :
    startFamilyJointMoment M L g = uniformSolutionMass (familyStartSystem M L g) (familyStartRhs L) := by
  unfold startFamilyJointMoment uniformSolutionMass cylinderProbability
  congr 1
  funext ω
  rw [indicator_product_eq_indicator]
  have hiff := familyStartSystem_eq_iff M L g hL ω
  simp only [Finset.mem_univ, forall_const, startIndicator_eq_true_iff]
  by_cases h : familyStartSystem M L g ω = familyStartRhs L
  · simp [h, hiff.mp h]
  · simp [h, mt hiff.mpr h]

omit [DecidableEq ι] in
theorem startFamilyJointMoment_pos_iff (M L : ℕ) (g : ι → ℕ) (hL : 0 < L) :
    0 < startFamilyJointMoment M L g ↔ Compatible (familyStartSystem M L g) (familyStartRhs L) := by
  rw [startFamilyJointMoment_eq_affineMass M L g hL, uniformSolutionMass_pos_iff]

omit [Fintype ι] [DecidableEq ι] in
theorem familyStartSystem_compatible_locally (M L : ℕ) (g : ι → ℕ)
    (hc : Compatible (familyStartSystem M L g) (familyStartRhs L)) :
    ∀ i, Compatible (startSystem M (g i) L) (startRhs L) := by
  obtain ⟨ω, hω⟩ := LinearMap.mem_range.mp hc
  intro i
  apply LinearMap.mem_range.mpr
  refine ⟨ω, ?_⟩
  funext j
  exact congrFun hω (i, j)

end PaperP1.Model
