module

public import PaperP1.Algebra.GradedVeroneseAlgebra
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # Every positively indexed Veronese inclusion is integral -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeroneseIntegral

open DirectSum

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G] (D : ℕ) (hD : 0 < D)

include hD in
theorem homogeneous_integral {n : ℕ} (a : A) (ha : a ∈ G n) :
    IsIntegral (GradedVeroneseAlgebra.veronese G D) a := by
  have haD : a ^ D ∈ G (n * D) := by
    simpa only [smul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded D ha
  have hm := GradedVeroneseAlgebra.piece_mem G D n haD
  apply IsIntegral.of_pow hD
  exact isIntegral_algebraMap (R := GradedVeroneseAlgebra.veronese G D) (A := A) (x := ⟨a ^ D, hm⟩)

include hD in
theorem integral : Algebra.IsIntegral (GradedVeroneseAlgebra.veronese G D) A := by
  classical
  refine ⟨fun a ↦ ?_⟩
  rw [← sum_support_decompose G a]
  exact IsIntegral.sum _ (fun n _ ↦ homogeneous_integral G D hD _ (decompose G a n).property)

end PaperP1.GradedVeroneseIntegral
