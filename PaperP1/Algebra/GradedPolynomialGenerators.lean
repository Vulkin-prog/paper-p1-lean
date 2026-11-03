module

public import PaperP1.Algebra.IrrelevantGenerated
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-! # The literal homogeneous polynomial presentation of an algebra generated in degree one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedPolynomialGenerators

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F A ι : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (H : ℕ → Submodule F A) [GradedAlgebra H] (g : ι → A) (hg : ∀ i, g i ∈ H 1)

include hg in
theorem eval_homogeneous (n : ℕ) (p : MvPolynomial ι F) (hp : p.IsHomogeneous n) :
    MvPolynomial.aeval g p ∈ H n := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (H n).zero_mem
  | add p q _hp _hq ihp ihq => simpa only [map_add] using (H n).add_mem ihp ihq
  | monomial d c hd =>
    have hd' : d.degree = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact hd
    rw [MvPolynomial.aeval_monomial]
    have hc : algebraMap F A c ∈ H 0 := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact (H 0).smul_mem c (SetLike.one_mem_graded H)
    have hp : d.prod (fun i k ↦ g i ^ k) ∈ H d.degree := by
      simpa only [Finsupp.prod, Finsupp.degree_apply, smul_eq_mul, mul_one] using
        (SetLike.prod_pow_mem_graded H (fun _ : ι ↦ (1 : ℕ)) g d (fun i _ ↦ hg i) (F := d.support))
    simpa only [zero_add, hd'] using SetLike.mul_mem_graded hc hp

def gradedEval : MvPolynomial.homogeneousSubmodule ι F →+*ᵍ H where
  __ := (MvPolynomial.aeval g).toRingHom
  map_mem hp := eval_homogeneous H g hg _ _ hp

theorem gradedEval_X (i : ι) : gradedEval H g hg (MvPolynomial.X i) = g i := MvPolynomial.aeval_X g i

include hg in
theorem eval_surjective (hgen : Algebra.adjoin F (Set.range g) = ⊤) :
    Function.Surjective (gradedEval H g hg) := by
  apply (AlgHom.range_eq_top (MvPolynomial.aeval g)).mp
  rw [MvPolynomial.aeval_range, hgen]

include hg in
theorem irrelevant_le_map (hgen : Algebra.adjoin F (Set.range g) = ⊤) :
    (HomogeneousIdeal.irrelevant H).toIdeal ≤
      ((HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule ι F)).toIdeal.map
        (gradedEval H g hg).toRingHom) := by
  rw [IrrelevantGenerated.irrelevant_eq_span H (Set.range g) (fun _ ⟨i, hi⟩ ↦ hi ▸ hg i) hgen]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hx := HomogeneousIdeal.mem_irrelevant_of_mem (MvPolynomial.homogeneousSubmodule ι F)
    (by decide : 0 < 1) (MvPolynomial.isHomogeneous_X F i)
  have hm := Ideal.mem_map_of_mem (gradedEval H g hg).toRingHom hx
  change gradedEval H g hg (MvPolynomial.X i) ∈
    ((HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule ι F)).toIdeal.map
      (gradedEval H g hg).toRingHom) at hm
  rw [gradedEval_X] at hm
  exact hm

end PaperP1.GradedPolynomialGenerators
