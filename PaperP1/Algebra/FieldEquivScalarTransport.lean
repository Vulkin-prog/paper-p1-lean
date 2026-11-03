module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Actual field extensions retain their degree and finite dimension under an explicit base-field equivalence -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FieldEquivScalarTransport

variable {K K' L : Type*} [Field K] [Field K'] [Field L] [Algebra K' L] (e : K ≃+* K')

@[instance_reducible] def algebra : Algebra K L := ((algebraMap K' L).comp e.toRingHom).toAlgebra

theorem algebraMap_eq (x : K) :
    letI := algebra (L := L) e
    algebraMap K L x = algebraMap K' L (e x) := rfl

theorem finrank_eq :
    letI := algebra (L := L) e
    Module.finrank K L = Module.finrank K' L := by
  let := algebra (L := L) e
  exact Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl L) rfl

theorem finite [Module.Finite K' L] :
    letI := algebra (L := L) e
    Module.Finite K L := by
  let := algebra (L := L) e
  apply Module.finite_of_finrank_pos
  rw [finrank_eq e]
  exact Module.finrank_pos

end PaperP1.FieldEquivScalarTransport
