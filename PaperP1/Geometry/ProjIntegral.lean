module

public import PaperP1.Algebra.GradedChartBasis
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.FunctionField

/-! # The actual projective spectrum of a graded domain is integral when nonempty -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjIntegral

open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace

variable {A σ : Type u} [CommRing A] [IsDomain A] [SetLike σ A] [AddSubgroupClass σ A]
  (G : ℕ → σ) [GradedRing G]

theorem localization_isDomain (M : Submonoid A) (hM : 0 ∉ M) :
    IsDomain (HomogeneousLocalization G M) := by
  have hle : M ≤ nonZeroDivisors A := by
    intro x hx
    apply mem_nonZeroDivisors_of_ne_zero
    intro hzero
    exact hM (hzero ▸ hx)
  have : IsDomain (Localization M) := IsLocalization.isDomain_localization hle
  exact (HomogeneousLocalization.val_injective (𝒜 := G) M).isDomain
    (algebraMap (HomogeneousLocalization G M) (Localization M))

theorem stalk_isDomain (p : ProjectiveSpectrum G) : IsDomain ((Proj G).presheaf.stalk p) := by
  have : IsDomain (AtPrime G p.asHomogeneousIdeal.toIdeal) :=
    localization_isDomain G _ (by
      change ¬ ((0 : A) ∉ p.asHomogeneousIdeal.toIdeal)
      exact not_not.mpr (Ideal.zero_mem _))
  exact (ConcreteCategory.bijective_of_isIso (AlgebraicGeometry.Proj.stalkIso G p).hom).injective.isDomain
    (AlgebraicGeometry.Proj.stalkIso G p).hom.hom

theorem isReduced : AlgebraicGeometry.IsReduced (Proj G) := by
  have (p : Proj G) : _root_.IsReduced ((Proj G).presheaf.stalk p) := by
    have := stalk_isDomain G p
    infer_instance
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk (Proj G)

def zeroPoint (hpos : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥) : ProjectiveSpectrum G where
  asHomogeneousIdeal := ⊥
  isPrime := by change (⊥ : Ideal A).IsPrime; infer_instance
  not_irrelevant_le h := hpos (by
    change (HomogeneousIdeal.irrelevant G).toIdeal = (⊥ : HomogeneousIdeal G).toIdeal
    exact congrArg HomogeneousIdeal.toIdeal (le_antisymm h bot_le))

theorem zero_generic (hpos : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥) :
    IsGenericPoint (zeroPoint G hpos) (Set.univ : Set (ProjectiveSpectrum G)) := by
  rw [isGenericPoint_def]
  apply Set.eq_univ_of_forall
  intro p
  apply (ProjectiveSpectrum.le_iff_mem_closure G (zeroPoint G hpos) p).mp
  change (⊥ : HomogeneousIdeal G) ≤ p.asHomogeneousIdeal
  exact bot_le

theorem irreducible (hpos : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥) :
    IrreducibleSpace (Proj G) :=
  (irreducibleSpace_def (Proj G)).mpr (zero_generic G hpos).isIrreducible

theorem integral (hpos : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥) :
    IsIntegral (Proj G) := by
  have := irreducible G hpos
  have := isReduced G
  exact AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced (Proj G)

theorem genericPoint_eq_zero (hpos : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥) :
    letI := irreducible G hpos
    genericPoint (Proj G) = zeroPoint G hpos := by
  let := irreducible G hpos
  exact (genericPoint_spec (Proj G)).eq (zero_generic G hpos)

omit [IsDomain A] in
theorem irrelevant_ne_bot_of_homogeneous {n : ℕ} (hn : 0 < n) {a : A}
    (ha : a ∈ G n) (ha0 : a ≠ 0) : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥ := by
  intro hzero
  have hm := HomogeneousIdeal.mem_irrelevant_of_mem G hn ha
  change a ∈ (HomogeneousIdeal.irrelevant G).toIdeal at hm
  rw [hzero, Ideal.mem_bot] at hm
  exact ha0 hm

end PaperP1.ProjIntegral
