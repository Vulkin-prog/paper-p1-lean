module

public import PaperP1.Algebra.TwoVariableGradedHilbert

/-! # Two actual finite linear parameters give a genuine Hilbert polynomial with nonnegative integer linear coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoParameterIntegralHilbertSlope

open Polynomial

theorem of_hyperplane {F B : Type*} [Field F] [CommRing B] [Algebra F B] [IsDomain B]
    (H : ℕ → Submodule F B) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    {b : B} (hb : b ∈ H 1) (hb0 : b ≠ 0)
    (hc : ∃ M c : ℕ, ∀ n : ℕ, M ≤ n → Module.finrank F (HomogeneousPrincipalQuotient.piece H b n) = c) :
    ∃ (d : ℕ) (β : ℚ), GradedHilbertPolynomial.IsHilbertPolynomial H (C (d : ℚ) * X + C β) := by
  obtain ⟨N, c, hN⟩ := hc
  have hs (n : ℕ) (hn : N ≤ n) : Module.finrank F (H (n + 1)) = Module.finrank F (H n) + c := by
    have he := HomogeneousPrincipalQuotient.finrank_add H hb hb0 n
    rw [hN (n + 1) (hn.trans (Nat.le_add_right n 1))] at he
    exact he.symm.trans (Nat.add_comm _ _)
  refine ⟨c, (Module.finrank F (H N) : ℚ) - (c : ℚ) * (N : ℚ), N, fun n hn ↦ ?_⟩
  have he := congrArg (Nat.cast : ℕ → ℚ)
    (GradedHilbertHyperplane.affine_of_difference (fun n ↦ Module.finrank F (H n)) N c hs n hn)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hn] at he
  simp only [eval_add, eval_mul, eval_C, eval_X]
  nlinarith

variable {F B ι : Type*} [Field F] [CommRing B] [Algebra F B] [IsDomain B]
  (H : ℕ → Submodule F B) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
  (g : Fin 2 → B) (hg : ∀ i, g i ∈ H 1)

local instance polynomialRing (σ : Type*) : CommRing (MvPolynomial σ F) := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra

include hg in
theorem of_generators [Fintype ι] (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))
    (hgen : ∀ b : B, ∃ a : ι → MvPolynomial (Fin 2) F, ∑ i, MvPolynomial.aeval g (a i) * v i = b) :
    ∃ (d : ℕ) (β : ℚ), GradedHilbertPolynomial.IsHilbertPolynomial H (C (d : ℚ) * X + C β) := by
  let := TwoParameterQuotientGenerators.grading H g hg
  let (n : ℕ) : Module.Finite F (TwoParameterQuotientGenerators.piece H g n) :=
    TwoParameterQuotientGenerators.piece_finite H g n
  have hc := UnivariateGradedModuleHilbert.eventually_constant
    (TwoParameterQuotientGenerators.piece H g)
    (TwoParameterQuotientGenerators.gradedOne H g hg)
    (TwoParameterQuotientGenerators.gradedOne_commutes H g hg)
    (fun i ↦ TwoParameterQuotientGenerators.quotientMap (F := F) g (v i)) w
    (TwoParameterQuotientGenerators.generator_mem H g v w hv)
    (TwoParameterQuotientGenerators.generators H g hg v hgen)
  by_cases hz : g 0 = 0
  · obtain ⟨M, c, hM⟩ := hc
    refine ⟨0, (c : ℚ), M, fun n hn ↦ ?_⟩
    simp only [Nat.cast_zero, C_0, zero_mul, zero_add, eval_C]
    rw [← TwoParameterQuotientGenerators.piece_finrank_of_zero H g hz n, hM n hn]
  · exact of_hyperplane H (hg 0) hz hc

include hg in
theorem of_finite (hfinite : (MvPolynomial.aeval (R := F) g).Finite) :
    ∃ (d : ℕ) (β : ℚ), GradedHilbertPolynomial.IsHilbertPolynomial H (C (d : ℚ) * X + C β) := by
  classical
  let := TwoVariableGradedHilbert.parameterAlgebra (F := F) g
  let : Module.Finite (MvPolynomial (Fin 2) F) B := hfinite
  obtain ⟨ι, hι, v, w, hv, hspan⟩ := FiniteHomogeneousModuleGenerators.exists_generators
    (A := MvPolynomial (Fin 2) F) H
  let := hι
  apply of_generators H g hg v w hv
  intro b
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial (Fin 2) F)).mp
    (show b ∈ Submodule.span (MvPolynomial (Fin 2) F) (Set.range v) by rw [hspan]; trivial)
  exact ⟨a, ha⟩

end PaperP1.TwoParameterIntegralHilbertSlope
