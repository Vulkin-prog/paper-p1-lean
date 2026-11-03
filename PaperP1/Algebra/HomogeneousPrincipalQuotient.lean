module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-! # The actual homogeneous quotient by one nonzero homogeneous equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousPrincipalQuotient

open DirectSum

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G] {e : ℕ} {f : A} (hf : f ∈ G e)

def ideal (f : A) : Ideal A := Ideal.span {f}

def piece (f : A) (n : ℕ) : Submodule F (A ⧸ ideal f) :=
  (G n).map (Ideal.Quotient.mkₐ F (ideal f)).toLinearMap

def quotientMap (f : A) (n : ℕ) : G n →ₗ[F] piece G f n where
  toFun x := ⟨Ideal.Quotient.mk (ideal f) x, Submodule.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  map_add' x y := Subtype.ext (map_add (Ideal.Quotient.mk (ideal f)) (x : A) (y : A))
  map_smul' a x := Subtype.ext ((Ideal.Quotient.mkₐ F (ideal f)).toLinearMap.map_smul a (x : A))

omit [GradedAlgebra G] in
theorem quotientMap_surjective (f : A) (n : ℕ) : Function.Surjective (quotientMap G f n) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
  exact ⟨⟨a, ha⟩, rfl⟩

def mulMap (n : ℕ) : G n →ₗ[F] G (n + e) where
  toFun x := ⟨(x : A) * f, SetLike.mul_mem_graded x.property hf⟩
  map_add' x y := Subtype.ext (add_mul (x : A) y f)
  map_smul' a x := Subtype.ext (Algebra.smul_mul_assoc a (x : A) f)

theorem mulMap_injective [IsDomain A] (hf0 : f ≠ 0) (n : ℕ) : Function.Injective (mulMap G hf n) := by
  intro x y h
  apply Subtype.ext
  exact mul_right_cancel₀ hf0 (congrArg Subtype.val h)

theorem range_mulMap (n : ℕ) : LinearMap.range (mulMap G hf n) = LinearMap.ker (quotientMap G f (n + e)) := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change Ideal.Quotient.mk (ideal f) ((a : A) * f) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩)
  · intro x hx
    have hz : Ideal.Quotient.mk (ideal f) (x : A) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    refine ⟨decompose G a n, ?_⟩
    apply Subtype.ext
    have he := DirectSum.coe_decompose_mul_add_of_right_mem G (a := a) (i := n) hf
    rw [ha, DirectSum.decompose_of_mem_same G x.property] at he
    exact he.symm

include hf in
theorem finrank_add [IsDomain A] (hf0 : f ≠ 0) (n : ℕ) [Module.Finite F (G (n + e))] :
    Module.finrank F (piece G f (n + e)) + Module.finrank F (G n) = Module.finrank F (G (n + e)) := by
  have hdim := (LinearMap.ker (quotientMap G f (n + e))).finrank_quotient_add_finrank
  rw [LinearEquiv.finrank_eq ((quotientMap G f (n + e)).quotKerEquivOfSurjective
    (quotientMap_surjective G f (n + e)))] at hdim
  have hr : Module.finrank F (LinearMap.ker (quotientMap G f (n + e))) = Module.finrank F (G n) := by
    rw [← range_mulMap G hf n]
    exact (LinearEquiv.ofInjective (mulMap G hf n) (mulMap_injective G hf hf0 n)).finrank_eq.symm
  rw [hr] at hdim
  exact hdim

end PaperP1.HomogeneousPrincipalQuotient
