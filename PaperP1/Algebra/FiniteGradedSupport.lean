module

public import PaperP1.Algebra.HomogeneousQuotientGrading
public import Lean.Elab.Tactic.Omega

/-! # A finite-dimensional genuinely graded algebra has only finitely many nonzero pieces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteGradedSupport

open DirectSum

theorem eventually_bot {F A : Type*} [Field F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → H n = ⊥ := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := F) (M := A)
  let T := S.biUnion (fun b ↦ (decompose H b).support)
  let N := T.sup id + 1
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro n hn
  have hzero (b : A) (hb : b ∈ S) : GradedAlgebra.proj H n b = 0 := by
    have hout : n ∉ (decompose H b).support := by
      intro hmem
      have hT : n ∈ T := Finset.mem_biUnion.mpr ⟨b, hb, hmem⟩
      have hle : n ≤ T.sup id := Finset.le_sup (f := id) hT
      dsimp [N] at hn
      omega
    rw [GradedAlgebra.proj_apply, DFinsupp.notMem_support_iff.mp hout, Submodule.coe_zero]
  have hker : Submodule.span F (S : Set A) ≤ LinearMap.ker (GradedAlgebra.proj H n) :=
    Submodule.span_le.mpr (fun b hb ↦ hzero b hb)
  rw [hS] at hker
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  have hz : GradedAlgebra.proj H n x = 0 := hker (show x ∈ (⊤ : Submodule F A) from trivial)
  simpa only [GradedAlgebra.proj_apply, decompose_of_mem_same H hx] using hz

theorem eventually_le_ideal {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H]
    (J : Ideal A) (hJ : J.IsHomogeneous H) [Module.Finite F (A ⧸ J)] :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → H n ≤ J.restrictScalars F := by
  let : GradedAlgebra (HomogeneousQuotientGrading.piece H J) := HomogeneousQuotientGrading.grading H J hJ
  obtain ⟨N, hN, hbot⟩ := eventually_bot (HomogeneousQuotientGrading.piece H J)
  refine ⟨N, hN, ?_⟩
  intro n hn x hx
  have hm : Ideal.Quotient.mk J x ∈ HomogeneousQuotientGrading.piece H J n :=
    Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hbot n hn] at hm
  exact Ideal.Quotient.eq_zero_iff_mem.mp hm

end PaperP1.FiniteGradedSupport
