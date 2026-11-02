module

public import PaperP1.Arithmetic.ShortBasisCycleReduction
public import PaperP1.Combinatorics.IncidenceBallGrowth
public import Mathlib.Data.Fintype.Option

/-! # An unconditional finite construction from actual medium-prime incidence columns -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortBasisFiniteConstruction

open Finset PaperP1.Arithmetic PaperP1.LocalDefectBound PaperP1.LargePrimeGraph
  PaperP1.MediumPrimeColumns PaperP1.MediumPrimeIncidence PaperP1.ShortBasisComponentStage
  PaperP1.ShortBasisCycleReduction PaperP1.BinaryIncidenceAugmentation
  PaperP1.BinaryIncidenceShortVectors PaperP1.GreedyShortKernel PaperP1.ShortIncidenceRoutes

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance (x y L : ℕ) : DecidableEq (largePrimeGraph x y L).ConnectedComponent := Classical.decEq _
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : AddCommGroup U :=
  Submodule.addCommGroup U
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : Module F₂ U := U.module

theorem incidence_column_points {P E : Type*} [DecidableEq P] (left right : E → Option P) (e : E) :
    finsuppIncidence left right (Finsupp.single e 1) = point (left e) + point (right e) := by
  rw [map_single]
  funext v
  have hp (a : Option P) : point a v = if v = a then 1 else 0 := by
    by_cases h : v = a
    · subst v
      simp [point]
    · simp [point, h]
  change edgeColumn (left e) (right e) v = point (left e) v + point (right e) v
  rw [hp, hp]
  rfl

theorem actual_short_vectors (x y L z M r d : ℕ)
    (hpow : (mediumPrimes L z).card + 1 < d ^ r) :
    ShortVectors x y L z M ((2 * d) * ((mediumPrimes L z).card + 1)) (2 * r + 1) := by
  classical
  obtain ⟨left, right, heq⟩ := actual_incidence_presentation x y L z M
  intro S hlarge
  obtain ⟨v, hv, hs, hk⟩ := IncidenceBallGrowth.dense_short_vector (finsuppIncidence left right)
    left right S r d (fun e _he ↦ incidence_column_points left right e)
    (by simpa only [Fintype.card_option, Fintype.card_coe] using hlarge)
    (by simpa only [Fintype.card_option, Fintype.card_coe] using hpow)
  have hzero : mediumFinsuppMap x y L z (retainedComponents x y L z M) v.val = 0 := by
    apply augment_injective
    have hi := (LinearMap.congr_fun heq v.val).symm.trans v.property
    exact hi.trans (map_zero augment).symm
  refine ⟨⟨v.val, hzero⟩, ?_, hs, hk⟩
  intro hz
  apply hv
  apply Subtype.ext
  exact congrArg (fun w : LinearMap.ker (mediumFinsuppMap x y L z
    (retainedComponents x y L z M)) ↦ w.val) hz

theorem complete_space (x y L z M r d : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hpow : (mediumPrimes L z).card + 1 < d ^ r) :
    ∃ (U : Submodule F₂ (retainedComponents x y L z M → F₂))
      (hU : U ≤ LinearMap.ker (actualMap x y L z (retainedComponents x y L z M)))
      (I : Type) (b : Module.Basis I F₂
        (ShortBasisFinalCut.CutSpace x y L z (retainedComponents x y L z M) U)),
      (retainedComponents x y L z M).card - (2 * d) * ((mediumPrimes L z).card + 1) -
          (primeCount z + 2) ≤
        Module.finrank F₂ (LinearMap.range (ShortBasisFinalCut.relationMap x y L z
          (retainedComponents x y L z M) hx hy (retained_subset_free x y L z M) U hU)) ∧
      (∀ i, (ShortBasisFinalCut.physicalMap x y L (retainedComponents x y L z M) U
        (b i).val).support.card ≤ M * (2 * r + 1) * (primeCount z + 3)) ∧
      Function.Injective ((ComponentProjectionInjectivity.firstProjection x y L
        (retainedComponents x y L z M)).comp (ShortBasisFinalCut.coefficientMap x y L z
          (retainedComponents x y L z M) U)) ∧
      Function.Injective ((ComponentProjectionInjectivity.secondProjection x y L
        (retainedComponents x y L z M)).comp (ShortBasisFinalCut.coefficientMap x y L z
          (retainedComponents x y L z M) U)) ∧
      Function.Injective ((ComponentProjectionInjectivity.firstClasses x y L
        (retainedComponents x y L z M)).comp (ShortBasisFinalCut.coefficientMap x y L z
          (retainedComponents x y L z M) U)) :=
  complete_space_from_short_vectors x y L z M ((2 * d) * ((mediumPrimes L z).card + 1))
    (2 * r + 1) hx hy (actual_short_vectors x y L z M r d hpow)

end PaperP1.ShortBasisFiniteConstruction
