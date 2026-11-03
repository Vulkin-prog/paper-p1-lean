module

public import PaperP1.Algebra.UnivariateHomogeneousPolynomial
public import PaperP1.Algebra.NatEventuallyConstant
public import PaperP1.Algebra.GradedModulePieceMap
public import PaperP1.Algebra.GradedHilbertPolynomial
public import Lean.Elab.Tactic.Omega

/-! # A finite homogeneous module over one degree-one parameter has an eventual constant Hilbert function -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnivariateGradedModuleHilbert

open Finset DirectSum Polynomial

variable {F B ι : Type*} [Field F] [CommRing B] [Algebra F B] [Fintype ι]
  (H : ℕ → Submodule F B) [GradedAlgebra H]

local instance polynomialRing : CommRing (MvPolynomial Unit F) := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra

variable (f : MvPolynomial.homogeneousSubmodule Unit F →+*ᵍ H)
  (hscalar : ∀ a : F, f (algebraMap F (MvPolynomial Unit F) a) = algebraMap F B a)

omit [GradedAlgebra H] in
theorem parameter_mem : f (MvPolynomial.X ()) ∈ H 1 :=
  f.map_mem (MvPolynomial.isHomogeneous_X F ())

include hscalar in
omit [GradedAlgebra H] in
theorem map_C (a : F) : f (MvPolynomial.C a) = algebraMap F B a := hscalar a

include hscalar in
omit [GradedAlgebra H] in
theorem map_homogeneous {n : ℕ} (p : MvPolynomial Unit F) (hp : p.IsHomogeneous n) :
    f p = algebraMap F B (p.coeff (Finsupp.single () n)) * f (MvPolynomial.X ()) ^ n := by
  calc
    f p = f (MvPolynomial.C (p.coeff (Finsupp.single () n)) * MvPolynomial.X () ^ n) :=
      congrArg f (UnivariateHomogeneousPolynomial.homogeneous_eq p hp)
    _ = _ := by rw [map_mul, map_pow, map_C H f hscalar]

variable (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))

include hscalar hv in
theorem representation
    (hgen : ∀ b : B, ∃ a : ι → MvPolynomial Unit F, ∑ i, f (a i) * v i = b)
    (n : ℕ) (hn : ∀ i, w i ≤ n) {b : B} (hb : b ∈ H n) :
    ∃ c : ι → F, ∑ i, c i • (f (MvPolynomial.X ()) ^ (n - w i) * v i) = b := by
  obtain ⟨a, ha⟩ := hgen b
  have he := GradedModulePieceMap.homogeneous_representation f v w hv n hn hb a ha
  let p (i : ι) := decompose (MvPolynomial.homogeneousSubmodule Unit F) (a i) (n - w i)
  let c (i : ι) := (p i : MvPolynomial Unit F).coeff (Finsupp.single () (n - w i))
  refine ⟨c, ?_⟩
  have hterm (i : ι) : f (p i) * v i = c i • (f (MvPolynomial.X ()) ^ (n - w i) * v i) := by
    rw [map_homogeneous H f hscalar (p i) (p i).property, Algebra.smul_def, mul_assoc]
  simpa only [p, hterm] using he

def mulMap (n : ℕ) : H n →ₗ[F] H (n + 1) where
  toFun b := ⟨f (MvPolynomial.X ()) * b, by
    have hm : f (MvPolynomial.X ()) * (b : B) ∈ H (1 + n) :=
      SetLike.mul_mem_graded (parameter_mem H f) b.property
    simpa only [Nat.add_comm 1 n] using hm⟩
  map_add' a b := Subtype.ext (mul_add _ (a : B) (b : B))
  map_smul' a b := Subtype.ext (Algebra.mul_smul_comm a _ (b : B))

include hscalar hv in
theorem mulMap_surjective
    (hgen : ∀ b : B, ∃ a : ι → MvPolynomial Unit F, ∑ i, f (a i) * v i = b)
    (n : ℕ) (hn : ∀ i, w i ≤ n) : Function.Surjective (mulMap H f n) := by
  intro b
  obtain ⟨c, hc⟩ := representation H f hscalar v w hv hgen (n + 1)
    (fun i ↦ (hn i).trans (Nat.le_add_right n 1)) b.property
  let p := ∑ i, c i • (f (MvPolynomial.X ()) ^ (n - w i) * v i)
  have hp : p ∈ H n := by
    apply (H n).sum_mem
    intro i _
    apply (H n).smul_mem
    have hm : f (MvPolynomial.X ()) ^ (n - w i) * v i ∈ H ((n - w i) + w i) := by
      exact SetLike.mul_mem_graded (by
        simpa only [smul_eq_mul, mul_one] using SetLike.pow_mem_graded (n - w i) (parameter_mem H f)) (hv i)
    simpa only [Nat.sub_add_cancel (hn i)] using hm
  refine ⟨⟨p, hp⟩, Subtype.ext ?_⟩
  change f (MvPolynomial.X ()) * p = (b : B)
  have ht (i : ι) : f (MvPolynomial.X ()) * (c i • (f (MvPolynomial.X ()) ^ (n - w i) * v i)) =
      c i • (f (MvPolynomial.X ()) ^ (n + 1 - w i) * v i) := by
    have he : n + 1 - w i = (n - w i) + 1 := by have := hn i; omega
    rw [Algebra.mul_smul_comm, ← mul_assoc, ← pow_succ', he]
  simpa only [p, Finset.mul_sum, ht] using hc

include hscalar hv in
theorem eventually_constant
    (hgen : ∀ b : B, ∃ a : ι → MvPolynomial Unit F, ∑ i, f (a i) * v i = b)
    [∀ n, Module.Finite F (H n)] : ∃ M c : ℕ, ∀ n : ℕ, M ≤ n → Module.finrank F (H n) = c := by
  classical
  let N := univ.sup w
  have hstep (n : ℕ) (hn : N ≤ n) : Module.finrank F (H (n + 1)) ≤ Module.finrank F (H n) :=
    LinearMap.finrank_le_finrank_of_surjective (mulMap_surjective H f hscalar v w hv hgen n
      (fun i ↦ (Finset.le_sup (f := w) (Finset.mem_univ i)).trans hn))
  obtain ⟨M, c, _, hc⟩ := NatEventuallyConstant.of_succ_le (fun n ↦ Module.finrank F (H n)) N hstep
  exact ⟨M, c, hc⟩

include hscalar hv in
theorem exists_polynomial
    (hgen : ∀ b : B, ∃ a : ι → MvPolynomial Unit F, ∑ i, f (a i) * v i = b)
    [∀ n, Module.Finite F (H n)] : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial H p := by
  obtain ⟨M, c, hc⟩ := eventually_constant H f hscalar v w hv hgen
  refine ⟨Polynomial.C (c : ℚ), M, fun n hn ↦ ?_⟩
  rw [Polynomial.eval_C, hc n hn]

end PaperP1.UnivariateGradedModuleHilbert
