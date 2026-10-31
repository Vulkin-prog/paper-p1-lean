module

public import PaperP1.Model.StartProbability
public import PaperP1.Affine.EffectiveRows

/-!
# Actual centered run moments and their effective full-support formula

Each start event is identified with its effective affine row space. Local
witnesses require compatibility explicitly. The Fourier sum and nullity
bound apply to the actual heterogeneous marginals in the finite prime cylinder.
Identification with square-class images and the infinite prime product measure
are separate obligations.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Algebra PaperP1.Probability PaperP1.Affine

namespace PaperP1.Model

local instance (P : Prop) : Decidable P := Classical.propDecidable P
local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def startFamilySpace (M L : ℕ) (g : ι → ℕ) (i : ι) :
    Submodule 𝔽₂ (SampleSpace M →ₗ[𝔽₂] 𝔽₂) :=
  effectiveRowSpace (startSystem M (g i) L)

instance startFamilySpaceFintype (M L : ℕ) (g : ι → ℕ) (i : ι) :
    Fintype (startFamilySpace M L g i) := effectiveRowSpaceFintype _

def startFamilyWitness (M L : ℕ) (g : ι → ℕ)
    (hc : ∀ i, Compatible (startSystem M (g i) L) (startRhs L)) (i : ι) : SampleSpace M :=
  affineWitness _ _ (hc i)

omit [Fintype ι] [DecidableEq ι] in
theorem startIndicator_eq_effective (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hc : ∀ i, Compatible (startSystem M (g i) L) (startRhs L)) (i : ι) (ω : SampleSpace M) :
    (indicatorValue (startIndicator (g i) L ω) : ℝ) =
      effectiveIndicator (startFamilySpace M L g i) (startFamilyWitness M L g hc i) ω := by
  classical
  have ha := affineWitness_solves (startSystem M (g i) L) (startRhs L) (hc i)
  have he := startSystem_eq_startRhs_iff (M := M) (x := g i) ω hL
  simp only [effectiveIndicator, startFamilySpace, effectiveRowEvent_iff,
    startFamilyWitness, ha]
  by_cases h : startSystem M (g i) L ω = startRhs L
  · simp [indicatorValue, startIndicator, h, he.mp h]
  · simp [indicatorValue, startIndicator, h, mt he.mpr h]

omit [Fintype ι] [DecidableEq ι] in
theorem exactMarginal_start_eq_effectiveRate (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hc : ∀ i, Compatible (startSystem M (g i) L) (startRhs L)) (i : ι) :
    exactMarginal (cylinderProbability M) (fun y => startIndicator y L) (g i) =
      effectiveRate (startFamilySpace M L g i) := by
  rw [exactMarginal_start_eq_affineMass M (g i) L hL]
  exact compatible_mass_eq_effectiveRate _ _ (hc i)

def startFamilyCenteredMoment (M L : ℕ) (g : ι → ℕ) : ℝ :=
  finiteExpectation (cylinderProbability M).weight (fun ω =>
    ∏ i, ((indicatorValue (startIndicator (g i) L ω) : ℝ) -
      exactMarginal (cylinderProbability M) (fun y => startIndicator y L) (g i)))

omit [DecidableEq ι] in
theorem startFamilyCenteredMoment_eq_effective (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hc : ∀ i, Compatible (startSystem M (g i) L) (startRhs L)) :
    startFamilyCenteredMoment M L g =
      effectiveCenteredMoment (startFamilySpace M L g) (startFamilyWitness M L g hc) := by
  unfold startFamilyCenteredMoment effectiveCenteredMoment cylinderProbability
  congr 1
  funext ω
  apply Finset.prod_congr rfl
  intro i _
  rw [startIndicator_eq_effective M L g hL hc i ω,
    ← exactMarginal_start_eq_effectiveRate M L g hL hc i]
  rfl

theorem start_full_support_formula (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hc : ∀ i, Compatible (startSystem M (g i) L) (startRhs L)) :
    startFamilyCenteredMoment M L g =
      (∏ i, exactMarginal (cylinderProbability M) (fun y => startIndicator y L) (g i)) *
        ∑ s : (i : ι) → startFamilySpace M L g i,
          if IsFullSupportRelation (startFamilySpace M L g) s then
            affineTupleSign (startFamilySpace M L g) (startFamilyWitness M L g hc) s
          else 0 := by
  simp_rw [exactMarginal_start_eq_effectiveRate M L g hL hc]
  rw [startFamilyCenteredMoment_eq_effective M L g hL hc, effectiveCenteredMoment,
    effective_full_support_formula]

theorem start_centered_moment_bound [Nonempty ι] (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hc : ∀ i, Compatible (startSystem M (g i) L) (startRhs L)) :
    |startFamilyCenteredMoment M L g| ≤
      (∏ i, exactMarginal (cylinderProbability M) (fun y => startIndicator y L) (g i)) *
        ((2 ^ relativeNullity (startFamilySpace M L g) : ℝ) - 1) := by
  simp_rw [exactMarginal_start_eq_effectiveRate M L g hL hc]
  rw [startFamilyCenteredMoment_eq_effective M L g hL hc]
  exact effectiveCenteredMoment_bound _ _

theorem start_full_support_relation_of_ne_zero (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hc : ∀ i, Compatible (startSystem M (g i) L) (startRhs L))
    (hn : startFamilyCenteredMoment M L g ≠ 0) :
    ∃ s : (i : ι) → startFamilySpace M L g i,
      IsFullSupportRelation (startFamilySpace M L g) s := by
  rw [startFamilyCenteredMoment_eq_effective M L g hL hc] at hn
  exact fullSupportRelation_of_centeredMoment_ne_zero _ _ hn

/-- The manuscript's finite-set centered coefficient is the same actual moment
after indexing its product by the finite subtype. -/
theorem dyadicCenteredMoment_eq_startFamily (N L : ℕ) (I : Finset ℕ) :
    dyadicCenteredMoment N L I =
      startFamilyCenteredMoment (dyadicCutoff N L) L (fun x : I => x.val) := by
  unfold dyadicCenteredMoment startFamilyCenteredMoment centeredMoment dyadicMarginal
  congr 1
  funext ω
  symm
  rw [Finset.univ_eq_attach]
  exact Finset.prod_attach I (fun x =>
    (indicatorValue (startIndicator x L ω) : ℝ) -
      exactMarginal (cylinderProbability (dyadicCutoff N L))
        (fun y => startIndicator y L) x)

end PaperP1.Model
