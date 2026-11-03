module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # The actual grading on a weighted polynomial quotient by a homogeneous ideal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedPolynomialQuotientGrading

open Finset DirectSum

variable {F σ : Type*} [CommRing F]

local instance polynomialRing : CommRing (MvPolynomial σ F) := inferInstance

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable (w : σ → ℕ) (I : Ideal (MvPolynomial σ F))

def piece (n : ℕ) : Submodule F (MvPolynomial σ F ⧸ I) :=
  (MvPolynomial.weightedHomogeneousSubmodule F w n).map (Ideal.Quotient.mkₐ F I).toLinearMap

variable (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule F w))

def component (n : ℕ) : (MvPolynomial σ F ⧸ I) →ₗ[F] (MvPolynomial σ F ⧸ I) :=
  (I.restrictScalars F).liftQ
    ((Ideal.Quotient.mkₐ F I).toLinearMap.comp (MvPolynomial.weightedHomogeneousComponent w n)) (by
      intro p hp
      change Ideal.Quotient.mk I (MvPolynomial.weightedHomogeneousComponent w n p) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact (MvPolynomial.mem_iff_weightedHomogeneousComponent_mem F w hI p).mp hp n)

theorem component_mk (n : ℕ) (p : MvPolynomial σ F) :
    component w I hI n (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk I (MvPolynomial.weightedHomogeneousComponent w n p) := rfl

theorem component_mem (n : ℕ) (x : MvPolynomial σ F ⧸ I) : component w I hI n x ∈ piece w I n := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Submodule.mem_map.mpr ⟨MvPolynomial.weightedHomogeneousComponent w n p,
    MvPolynomial.weightedHomogeneousComponent_mem w p n, rfl⟩

theorem component_piece (n m : ℕ) {x : MvPolynomial σ F ⧸ I} (hx : x ∈ piece w I m) :
    component w I hI n x = if n = m then x else 0 := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
  change component w I hI n (Ideal.Quotient.mk I p) = if n = m then Ideal.Quotient.mk I p else 0
  rw [component_mk, MvPolynomial.weightedHomogeneousComponent_of_mem hp]
  split_ifs
  · rfl
  · exact map_zero _

theorem component_recompose (n : ℕ) (a : ⨁ m, piece w I m) :
    component w I hI n (DirectSum.coeAddMonoidHom (piece w I) a) = (a n : MvPolynomial σ F ⧸ I) := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply, Submodule.coe_zero]
  | of m x =>
    rw [DirectSum.coeAddMonoidHom_of, component_piece w I hI n m x.property, DirectSum.coe_of_apply]
    by_cases hnm : n = m <;> simp only [hnm, eq_comm, ite_true, ite_false]; rfl
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]
    rfl

include hI in
theorem recompose_injective : Function.Injective (DirectSum.coeAddMonoidHom (piece w I)) := by
  intro a b hab
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  rw [← component_recompose w I hI n a, ← component_recompose w I hI n b, hab]

theorem recompose_surjective : Function.Surjective (DirectSum.coeAddMonoidHom (piece w I)) := by
  classical
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  let S := (MvPolynomial.weightedHomogeneousComponent_finsupp (w := w) p).toFinset
  let a : ⨁ n, piece w I n := ∑ n ∈ S, DirectSum.of (fun m ↦ piece w I m) n
    ⟨Ideal.Quotient.mk I (MvPolynomial.weightedHomogeneousComponent w n p),
      Submodule.mem_map.mpr ⟨MvPolynomial.weightedHomogeneousComponent w n p,
        MvPolynomial.weightedHomogeneousComponent_mem w p n, rfl⟩⟩
  refine ⟨a, ?_⟩
  simp only [a, map_sum, DirectSum.coeAddMonoidHom_of]
  change (∑ n ∈ S, Ideal.Quotient.mk I (MvPolynomial.weightedHomogeneousComponent w n p)) =
    Ideal.Quotient.mk I p
  rw [← map_sum]
  apply congrArg (Ideal.Quotient.mk I)
  exact (finsum_eq_sum _ (MvPolynomial.weightedHomogeneousComponent_finsupp (w := w) p)).symm.trans
    (MvPolynomial.sum_weightedHomogeneousComponent w p)

include hI in
theorem isInternal : DirectSum.IsInternal (piece w I) :=
  ⟨recompose_injective w I hI, recompose_surjective w I⟩

@[instance_reducible] def decomposition : DirectSum.Decomposition (piece w I) :=
  (isInternal w I hI).chooseDecomposition

theorem gradedMonoid : SetLike.GradedMonoid (piece w I) where
  one_mem := by
    exact Submodule.mem_map.mpr ⟨1, MvPolynomial.isWeightedHomogeneous_one F w,
      (Ideal.Quotient.mkₐ F I).map_one⟩
  mul_mem := by
    intro n m x y hx hy
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨p * q, hp.mul hq, (Ideal.Quotient.mkₐ F I).map_mul p q⟩

@[instance_reducible] def gradedAlgebra : GradedAlgebra (piece w I) where
  toDecomposition := decomposition w I hI
  toGradedMonoid := gradedMonoid w I

theorem piece_zero_iff (hw : ∀ i, w i ≠ 0) (x : MvPolynomial σ F ⧸ I) :
    x ∈ piece w I 0 ↔ ∃ c : F, algebraMap F (MvPolynomial σ F ⧸ I) c = x := by
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    have hh := (MvPolynomial.mem_weightedHomogeneousSubmodule F w 0 p).mp hp
    have he := hh.weightedHomogeneousComponent_same
    rw [MvPolynomial.weightedHomogeneousComponent_zero p hw] at he
    refine ⟨p.coeff 0, ?_⟩
    change Ideal.Quotient.mk I (MvPolynomial.C (p.coeff 0)) = Ideal.Quotient.mk I p
    exact congrArg (Ideal.Quotient.mk I) he
  · rintro ⟨c, rfl⟩
    exact Submodule.mem_map.mpr ⟨MvPolynomial.C c, MvPolynomial.isWeightedHomogeneous_C w c, rfl⟩

end PaperP1.WeightedPolynomialQuotientGrading
