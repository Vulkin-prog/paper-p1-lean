module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # An actual linear map between finite coefficient arrays has a nonzero kernel when the target is smaller -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteFunctionLinearKernel

theorem exists_nonzero_kernel {F I J : Type*} [Field F] [Fintype I] [Fintype J]
    (T : (I → F) →ₗ[F] (J → F)) (hcard : Fintype.card J < Fintype.card I) :
    ∃ c : I → F, c ≠ 0 ∧ T c = 0 := by
  have hdim : Module.finrank F (J → F) < Module.finrank F (I → F) := by
    simpa only [Module.finrank_pi] using hcard
  have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := T) hdim
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp hk
  exact ⟨c, hc0, hc⟩

end PaperP1.FiniteFunctionLinearKernel
