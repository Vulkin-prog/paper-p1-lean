module

public import PaperP1.Algebra.HomogeneousQuotientGrading
public import PaperP1.Algebra.HomogeneousPrincipalQuotient
public import PaperP1.Algebra.GradedPolynomialGenerators
public import Mathlib.Tactic.FinCases

/-! # Killing one of two actual degree-one parameters leaves a one-parameter graded module -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoParameterQuotientGenerators

open Finset

variable {F B : Type*} [Field F] [CommRing B] [Algebra F B]
  (H : ℕ → Submodule F B) [GradedAlgebra H] (g : Fin 2 → B) (hg : ∀ i, g i ∈ H 1)

local instance polynomialRing (σ : Type*) : CommRing (MvPolynomial σ F) := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra

def ideal : Ideal B := Ideal.span {g 0}
abbrev Quotient := B ⧸ ideal g
local instance quotientRing : CommRing (Quotient g) := inferInstance

def quotientMap : B →ₐ[F] Quotient g := Ideal.Quotient.mkₐ F (ideal g)

def piece (n : ℕ) : Submodule F (Quotient g) := HomogeneousQuotientGrading.piece H (ideal g) n

include hg in
theorem ideal_homogeneous : (ideal g).IsHomogeneous H := by
  apply Ideal.homogeneous_span
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact ⟨1, hg 0⟩

@[instance_reducible] def grading : GradedAlgebra (piece H g) :=
  HomogeneousQuotientGrading.grading H (ideal g) (ideal_homogeneous H g hg)

omit [GradedAlgebra H] in
theorem parameter_zero : quotientMap (F := F) g (g 0) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (g 0))

def killFirst (F : Type*) [Field F] : MvPolynomial (Fin 2) F →ₐ[F] MvPolynomial Unit F :=
  MvPolynomial.aeval (fun i ↦ if i = 0 then 0 else MvPolynomial.X ())

theorem killFirst_X (i : Fin 2) : killFirst F (MvPolynomial.X i) =
    if i = 0 then 0 else MvPolynomial.X () := MvPolynomial.aeval_X _ i

def evalOne : MvPolynomial Unit F →ₐ[F] Quotient g :=
  MvPolynomial.aeval (fun _ : Unit ↦ quotientMap (F := F) g (g 1))

def gradedOne : MvPolynomial.homogeneousSubmodule Unit F →+*ᵍ piece H g := by
  letI := grading H g hg
  exact GradedPolynomialGenerators.gradedEval (piece H g)
    (fun _ : Unit ↦ quotientMap (F := F) g (g 1))
    (fun _ ↦ Submodule.mem_map.mpr ⟨g 1, hg 1, rfl⟩)

omit [GradedAlgebra H] in
theorem factor : (quotientMap (F := F) g).comp (MvPolynomial.aeval g) =
    (evalOne (F := F) g).comp (killFirst F) := by
  apply MvPolynomial.algHom_ext
  intro i
  change quotientMap (F := F) g (MvPolynomial.aeval g (MvPolynomial.X i)) =
    evalOne (F := F) g (killFirst F (MvPolynomial.X i))
  rw [MvPolynomial.aeval_X, killFirst_X]
  fin_cases i
  · change quotientMap (F := F) g (g 0) = evalOne (F := F) g 0
    rw [map_zero, parameter_zero]
  · change quotientMap (F := F) g (g 1) = evalOne (F := F) g (MvPolynomial.X ())
    exact (MvPolynomial.aeval_X (fun _ : Unit ↦ quotientMap (F := F) g (g 1)) ()).symm

omit [GradedAlgebra H] in
theorem factor_apply (p : MvPolynomial (Fin 2) F) :
    quotientMap (F := F) g (MvPolynomial.aeval g p) = evalOne (F := F) g (killFirst F p) :=
  DFunLike.congr_fun (factor (F := F) g) p

theorem gradedOne_commutes (a : F) :
    gradedOne H g hg (algebraMap F (MvPolynomial Unit F) a) = algebraMap F (Quotient g) a :=
  (evalOne (F := F) g).commutes a

variable {ι : Type*} [Fintype ι] (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))

theorem generators
    (hgen : ∀ b : B, ∃ a : ι → MvPolynomial (Fin 2) F, ∑ i, MvPolynomial.aeval g (a i) * v i = b) :
    ∀ b : Quotient g, ∃ a : ι → MvPolynomial Unit F,
      ∑ i, gradedOne H g hg (a i) * quotientMap (F := F) g (v i) = b := by
  intro b
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨a, ha⟩ := hgen x
  refine ⟨fun i ↦ killFirst F (a i), ?_⟩
  have he := congrArg (quotientMap (F := F) g) ha
  simp only [map_sum, map_mul, factor_apply] at he
  exact he

include hv in
omit [GradedAlgebra H] [Fintype ι] in
theorem generator_mem (i : ι) : quotientMap (F := F) g (v i) ∈ piece H g (w i) :=
  Submodule.mem_map.mpr ⟨v i, hv i, rfl⟩

omit [GradedAlgebra H] in
theorem piece_finite (n : ℕ) [Module.Finite F (H n)] : Module.Finite F (piece H g n) :=
  HomogeneousQuotientGrading.piece_finite H (ideal g) n

omit [GradedAlgebra H] in
theorem piece_finrank_of_zero (hzero : g 0 = 0) (n : ℕ) :
    Module.finrank F (piece H g n) = Module.finrank F (H n) := by
  let q := HomogeneousPrincipalQuotient.quotientMap H (g 0) n
  have hinj : Function.Injective q := by
    intro x y hxy
    apply Subtype.ext
    have he : Ideal.Quotient.mk (HomogeneousPrincipalQuotient.ideal (g 0)) (x : B) =
        Ideal.Quotient.mk (HomogeneousPrincipalQuotient.ideal (g 0)) (y : B) := congrArg Subtype.val hxy
    have hz : Ideal.Quotient.mk (HomogeneousPrincipalQuotient.ideal (g 0)) ((x : B) - y) = 0 := by
      rw [map_sub, he, sub_self]
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
    rw [HomogeneousPrincipalQuotient.ideal, hzero, Ideal.span_singleton_zero, Ideal.mem_bot] at hm
    exact sub_eq_zero.mp hm
  exact (LinearEquiv.ofBijective q ⟨hinj, HomogeneousPrincipalQuotient.quotientMap_surjective H (g 0) n⟩).finrank_eq.symm

end PaperP1.TwoParameterQuotientGenerators
