module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-! # The actual quotient grading for an arbitrary homogeneous ideal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousQuotientGrading

open Finset DirectSum

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G] (I : Ideal A) (hI : I.IsHomogeneous G)

def piece (n : ℕ) : Submodule F (A ⧸ I) :=
  (G n).map (Ideal.Quotient.mkₐ F I).toLinearMap

def component (n : ℕ) : (A ⧸ I) →ₗ[F] (A ⧸ I) :=
  (I.restrictScalars F).liftQ
    ((Ideal.Quotient.mkₐ F I).toLinearMap.comp (GradedAlgebra.proj G n)) (by
      intro a ha
      change Ideal.Quotient.mk I (decompose G a n : A) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hI.mem_iff.mp ha) n))

theorem component_mk (n : ℕ) (a : A) : component G I hI n (Ideal.Quotient.mk I a) =
    Ideal.Quotient.mk I (decompose G a n : A) := rfl

theorem component_mem (n : ℕ) (x : A ⧸ I) : component G I hI n x ∈ piece G I n := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Submodule.mem_map.mpr ⟨decompose G a n, (decompose G a n).property, rfl⟩

theorem component_piece (n m : ℕ) {x : A ⧸ I} (hx : x ∈ piece G I m) :
    component G I hI n x = if n = m then x else 0 := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
  change component G I hI n (Ideal.Quotient.mk I a) = if n = m then Ideal.Quotient.mk I a else 0
  rw [component_mk]
  by_cases hnm : n = m
  · subst n
    rw [ite_eq_left rfl, decompose_of_mem_same G ha]
  · rw [ite_eq_right hnm, decompose_of_mem_ne G ha (Ne.symm hnm), map_zero]

theorem component_recompose (n : ℕ) (a : ⨁ m, piece G I m) :
    component G I hI n (DirectSum.coeAddMonoidHom (piece G I) a) = (a n : A ⧸ I) := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply, Submodule.coe_zero]
  | of m x =>
    rw [DirectSum.coeAddMonoidHom_of, component_piece G I hI n m x.property, DirectSum.coe_of_apply]
    by_cases hnm : n = m <;> simp only [hnm, eq_comm, ite_true, ite_false]; rfl
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]
    rfl

include hI in
theorem recompose_injective : Function.Injective (DirectSum.coeAddMonoidHom (piece G I)) := by
  intro a b hab
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  rw [← component_recompose G I hI n a, ← component_recompose G I hI n b, hab]

theorem recompose_surjective : Function.Surjective (DirectSum.coeAddMonoidHom (piece G I)) := by
  classical
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  let z : ⨁ n, piece G I n := ∑ n ∈ (decompose G a).support, DirectSum.of (fun m ↦ piece G I m) n
    ⟨Ideal.Quotient.mk I (decompose G a n : A),
      Submodule.mem_map.mpr ⟨decompose G a n, (decompose G a n).property, rfl⟩⟩
  refine ⟨z, ?_⟩
  simp only [z, map_sum, DirectSum.coeAddMonoidHom_of]
  change (∑ n ∈ (decompose G a).support, Ideal.Quotient.mk I (decompose G a n : A)) =
    Ideal.Quotient.mk I a
  rw [← map_sum, sum_support_decompose]

include hI in
theorem isInternal : DirectSum.IsInternal (piece G I) :=
  ⟨recompose_injective G I hI, recompose_surjective G I⟩

theorem gradedMonoid : SetLike.GradedMonoid (piece G I) where
  one_mem := Submodule.mem_map.mpr ⟨1, SetLike.one_mem_graded G, (Ideal.Quotient.mkₐ F I).map_one⟩
  mul_mem := by
    intro n m x y hx hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨a * b, SetLike.mul_mem_graded ha hb, (Ideal.Quotient.mkₐ F I).map_mul a b⟩

@[instance_reducible] def grading : GradedAlgebra (piece G I) where
  toDecomposition := (isInternal G I hI).chooseDecomposition
  toGradedMonoid := gradedMonoid G I

def mk : G →+*ᵍ piece G I where
  __ := Ideal.Quotient.mk I
  map_mem hx := Submodule.mem_map.mpr ⟨_, hx, rfl⟩

omit [GradedAlgebra G] in
theorem mk_surjective : Function.Surjective (mk G I) := Ideal.Quotient.mk_surjective

omit [GradedAlgebra G] in
theorem mk_commutes (a : F) : mk G I (algebraMap F A a) = algebraMap F (A ⧸ I) a := rfl

omit [GradedAlgebra G] in
theorem piece_finite (n : ℕ) [Module.Finite F (G n)] : Module.Finite F (piece G I n) :=
  Module.Finite.map (G n) (Ideal.Quotient.mkₐ F I).toLinearMap

include hI in
theorem component_eq_proj (n : ℕ) (x : A ⧸ I) :
    letI := grading G I hI
    component G I hI n x = GradedAlgebra.proj (piece G I) n x := by
  let := grading G I hI
  have h := component_recompose G I hI n (decompose (piece G I) x)
  change component G I hI n ((decompose (piece G I)).symm (decompose (piece G I) x)) = _ at h
  rw [Equiv.symm_apply_apply] at h
  exact h

end PaperP1.HomogeneousQuotientGrading
