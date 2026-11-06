module

public import PaperP1.Geometry.LinearHypersurfaceImage
public import PaperP1.Algebra.HomogeneousMonicGenerator
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Polynomial.Tower
public import Mathlib.RingTheory.Ideal.Maximal

/-! # Actual finite-dimensional linear images have a principal homogeneous irreducible equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearHypersurfaceMinimalEquation

open MvPolynomial LinearHypersurfaceImage
attribute [local instance] MvPolynomial.gradedAlgebra

variable {m : ℕ} {F A : Type*} [Field F] [CommRing A]

local instance polynomialRing (σ : Type*) : CommRing (MvPolynomial σ F) := inferInstance
local instance polynomialSemiring (σ : Type*) : Semiring (MvPolynomial σ F) :=
  (polynomialRing σ).toSemiring

variable [Algebra (MvPolynomial (Fin m) F) A]

def equation (y : A) : MvPolynomial (Fin (m + 1)) F :=
  (finSuccEquiv F m).symm (minpoly (MvPolynomial (Fin m) F) y)

theorem equation_monic (y : A) (hy : IsIntegral (MvPolynomial (Fin m) F) y) :
    (finSuccEquiv F m (equation (m := m) (F := F) y)).Monic := by
  rw [equation, AlgEquiv.apply_symm_apply]
  exact minpoly.monic hy

theorem equation_nonzero (y : A) (hy : IsIntegral (MvPolynomial (Fin m) F) y) :
    equation (m := m) (F := F) y ≠ 0 := by
  intro hz
  apply (minpoly.monic hy).ne_zero
  have he := congrArg (finSuccEquiv F m) hz
  simpa only [equation, AlgEquiv.apply_symm_apply, map_zero] using he

variable [Algebra F A] [IsScalarTower F (MvPolynomial (Fin m) F) A]

theorem evaluation_factor (g : Fin m → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom) :
    aeval (R := F) (coordinates g y) =
      ((Polynomial.aeval y).restrictScalars F).comp (finSuccEquiv F m).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change aeval (coordinates g y) (X 0) = Polynomial.aeval y (finSuccEquiv F m (X 0))
    rw [aeval_X, finSuccEquiv_X_zero, Polynomial.aeval_X]
    rfl
  · change aeval (coordinates g y) (X j.succ) = Polynomial.aeval y (finSuccEquiv F m (X j.succ))
    rw [aeval_X, finSuccEquiv_X_succ, Polynomial.aeval_C, DFunLike.congr_fun hsource (X j)]
    change coordinates g y j.succ = aeval g (X j)
    rw [aeval_X]
    rfl

variable [IsDomain A] [Module.IsTorsionFree (MvPolynomial (Fin m) F) A]

theorem principal (g : Fin m → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (hy : IsIntegral (MvPolynomial (Fin m) F) y) :
    ideal (F := F) g y = Ideal.span {equation (m := m) (F := F) y} := by
  ext P
  rw [Ideal.mem_span_singleton]
  change aeval (coordinates g y) P = 0 ↔ equation (m := m) (F := F) y ∣ P
  rw [evaluation_factor g y hsource]
  change Polynomial.aeval y (finSuccEquiv F m P) = 0 ↔ equation (m := m) (F := F) y ∣ P
  rw [minpoly.isIntegrallyClosed_dvd_iff hy]
  have he : finSuccEquiv F m (equation (m := m) (F := F) y) = minpoly (MvPolynomial (Fin m) F) y :=
    (finSuccEquiv F m).apply_symm_apply _
  rw [← he]
  exact map_dvd_iff (finSuccEquiv F m)

theorem equation_irreducible (g : Fin m → A) (y : A)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (hy : IsIntegral (MvPolynomial (Fin m) F) y) : Irreducible (equation (m := m) (F := F) y) := by
  apply Prime.irreducible
  apply (Ideal.span_singleton_prime (equation_nonzero y hy)).mp
  rw [← principal g y hsource hy]
  exact ideal_prime g y

theorem equation_homogeneous (H : ℕ → Submodule F A) [GradedAlgebra H]
    (g : Fin m → A) (hg : ∀ i, g i ∈ H 1) (y : A) (hy : y ∈ H 1)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (hint : IsIntegral (MvPolynomial (Fin m) F) y) :
    (equation (m := m) (F := F) y).IsHomogeneous (minpoly (MvPolynomial (Fin m) F) y).natDegree := by
  have hI : (Ideal.span {equation (m := m) (F := F) y}).IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) F) := by
    rw [← principal g y hsource hint]
    exact ideal_homogeneous H g hg y hy
  simpa only [equation, AlgEquiv.apply_symm_apply] using
    HomogeneousMonicGenerator.homogeneous (equation (m := m) (F := F) y) hI (equation_monic y hint)

theorem equation_totalDegree (H : ℕ → Submodule F A) [GradedAlgebra H]
    (g : Fin m → A) (hg : ∀ i, g i ∈ H 1) (y : A) (hy : y ∈ H 1)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (hint : IsIntegral (MvPolynomial (Fin m) F) y) :
    (equation (m := m) (F := F) y).totalDegree = (minpoly (MvPolynomial (Fin m) F) y).natDegree :=
  (equation_homogeneous H g hg y hy hsource hint).totalDegree (equation_nonzero y hint)

variable {K L : Type*} [Field K] [Field L]
  [Algebra (MvPolynomial (Fin m) F) K] [Algebra K L] [Algebra A L]
  [Algebra (MvPolynomial (Fin m) F) L]
  [IsScalarTower (MvPolynomial (Fin m) F) K L]
  [IsScalarTower (MvPolynomial (Fin m) F) A L]
  [IsFractionRing (MvPolynomial (Fin m) F) K]

omit [Algebra F A] [IsScalarTower F (MvPolynomial (Fin m) F) A]
  [Module.IsTorsionFree (MvPolynomial (Fin m) F) A] in
theorem degree_from_fraction_field (y : A) (hy : IsIntegral (MvPolynomial (Fin m) F) y) :
    (minpoly (MvPolynomial (Fin m) F) y).natDegree =
      (minpoly K (algebraMap A L y)).natDegree := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hy]
  exact (Polynomial.natDegree_map_eq_of_injective
    (IsFractionRing.injective (MvPolynomial (Fin m) F) K) _).symm

theorem equation_degree_of_primitive [FiniteDimensional K L]
    (H : ℕ → Submodule F A) [GradedAlgebra H]
    (g : Fin m → A) (hg : ∀ i, g i ∈ H 1) (y : A) (hy : y ∈ H 1)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (hint : IsIntegral (MvPolynomial (Fin m) F) y)
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤) :
    (equation (m := m) (F := F) y).totalDegree = Module.finrank K L := by
  rw [equation_totalDegree H g hg y hy hsource hint,
    degree_from_fraction_field (K := K) (L := L) y hint]
  exact (Field.primitive_element_iff_minpoly_natDegree_eq K _).mp hprimitive

omit [Module.IsTorsionFree (MvPolynomial (Fin m) F) A] in
theorem equation_of_finite_primitive [FiniteDimensional K L]
    (H : ℕ → Submodule F A) [GradedAlgebra H]
    (g : Fin m → A) (hg : ∀ i, g i ∈ H 1) (y : A) (hy : y ∈ H 1)
    (hsource : algebraMap (MvPolynomial (Fin m) F) A = (aeval (R := F) g).toRingHom)
    (hfinite : (aeval (R := F) g).Finite) (hinj : Function.Injective (aeval (R := F) g))
    (hprimitive : IntermediateField.adjoin K {algebraMap A L y} = ⊤) :
    ∃ q : MvPolynomial (Fin (m + 1)) F, ideal (F := F) g y = Ideal.span {q} ∧
      Irreducible q ∧ q.IsHomogeneous (Module.finrank K L) ∧
      q.totalDegree = Module.finrank K L ∧ (finSuccEquiv F m q).Monic := by
  have hmapinj : Function.Injective (algebraMap (MvPolynomial (Fin m) F) A) := by
    rw [hsource]
    exact hinj
  let : FaithfulSMul (MvPolynomial (Fin m) F) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hmapinj
  let : Module.IsTorsionFree (MvPolynomial (Fin m) F) A := inferInstance
  have hfin : Module.Finite (MvPolynomial (Fin m) F) A := by
    apply RingHom.finite_algebraMap.mp
    rw [hsource]
    exact hfinite
  let : Module.Finite (MvPolynomial (Fin m) F) A := hfin
  have hint : IsIntegral (MvPolynomial (Fin m) F) y := IsIntegral.of_finite _ y
  have hdegree := equation_degree_of_primitive H g hg y hy hsource hint hprimitive
  have hnat : (minpoly (MvPolynomial (Fin m) F) y).natDegree = Module.finrank K L :=
    (equation_totalDegree H g hg y hy hsource hint).symm.trans hdegree
  refine ⟨equation (m := m) (F := F) y, principal g y hsource hint,
    equation_irreducible g y hsource hint, ?_, hdegree, equation_monic y hint⟩
  rw [← hnat]
  exact equation_homogeneous H g hg y hy hsource hint

end PaperP1.LinearHypersurfaceMinimalEquation
