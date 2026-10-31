module

public import PaperP1.Model.JointStartSystem
public import PaperP1.Affine.RelativeWeights
public import PaperP1.Model.SquareClassRelations

/-!
# Exact joint probabilities and relative rank loss

A compatible intersection has probability `2^ρ` times the product of the
actual local marginals. An incompatible intersection has probability zero.
The nullity is that of the effective square-class spaces when the cutoff
covers every block.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability

namespace PaperP1.Model

local instance jointStartProbabilityPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance jointStartProbabilityDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem startFamilyJointMoment_of_compatible (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hc : Compatible (familyStartSystem M L g) (familyStartRhs L)) :
    startFamilyJointMoment M L g =
      (2 ^ relativeNullity (startFamilySpace M L g) : ℝ) *
        (∏ i, exactMarginal (cylinderProbability M) (fun y => startIndicator y L) (g i)) := by
  have hlocal := familyStartSystem_compatible_locally M L g hc
  have hmarg (i : ι) := exactMarginal_start_eq_effectiveRate M L g hL hlocal i
  simp_rw [hmarg]
  rw [relative_weight_eq_total_rank, startFamilyJointMoment_eq_affineMass M L g hL,
    compatible_mass_eq_effectiveRate _ _ hc, effectiveRate,
    card_eq_two_pow_finrank (V := effectiveRowSpace (familyStartSystem M L g)),
    effectiveRowSpace_familyStartSystem]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

omit [DecidableEq ι] in
theorem startFamilyJointMoment_of_not_compatible (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hc : ¬Compatible (familyStartSystem M L g) (familyStartRhs L)) :
    startFamilyJointMoment M L g = 0 := by
  rw [startFamilyJointMoment_eq_affineMass M L g hL]
  exact uniformSolutionMass_of_not_compatible _ _ hc

theorem startFamilyJointMoment_of_pos (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hq : 0 < startFamilyJointMoment M L g) :
    startFamilyJointMoment M L g =
      (2 ^ relativeNullity (startFamilySpace M L g) : ℝ) *
        (∏ i, exactMarginal (cylinderProbability M) (fun y => startIndicator y L) (g i)) :=
  startFamilyJointMoment_of_compatible M L g hL ((startFamilyJointMoment_pos_iff M L g hL).mp hq)

theorem startFamilyJointMoment_squareClass_of_pos (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hq : 0 < startFamilyJointMoment M L g) :
    startFamilyJointMoment M L g =
      (2 ^ relativeNullity (squareClassFamilySpace L g) : ℝ) *
        (∏ i, exactMarginal (cylinderProbability M) (fun y => startIndicator y L) (g i)) := by
  rw [relativeNullity_squareClassFamily_eq_rows M L g hcut]
  exact startFamilyJointMoment_of_pos M L g hL hq

end PaperP1.Model
