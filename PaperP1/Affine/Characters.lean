module

public import PaperP1.Affine.Fourier
public import PaperP1.Probability.UniformFinite

/-!
# Characters indexed by effective spaces of linear forms

An effective space is an actual subspace of the dual, so distinct elements
represent distinct characters. Affine signs are evaluations at a chosen local
solution. Orthogonality gives the indicator and its exact actual marginal.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Algebra PaperP1.Probability

namespace PaperP1.Affine

local instance (P : Prop) : Decidable P := Classical.propDecidable P

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V : Type*} [AddCommGroup V] [Module 𝔽₂ V]

/-- A real binary character on the finite sign space. -/
def realCharacter (f : V →ₗ[𝔽₂] 𝔽₂) (v : V) : ℝ := (binarySign (f v) : ℝ)

@[simp]
theorem realCharacter_zero (v : V) : realCharacter (0 : V →ₗ[𝔽₂] 𝔽₂) v = 1 := by
  simp [realCharacter]

theorem realCharacter_add (f g : V →ₗ[𝔽₂] 𝔽₂) (v : V) :
    realCharacter (f + g) v = realCharacter f v * realCharacter g v := by
  simp [realCharacter, binarySign_add]

theorem realCharacter_sub_argument (f : V →ₗ[𝔽₂] 𝔽₂) (v a : V) :
    realCharacter f (v - a) = realCharacter f v * realCharacter f a := by
  simp [realCharacter, binarySign_sub]

theorem abs_realCharacter (f : V →ₗ[𝔽₂] 𝔽₂) (v : V) :
    |realCharacter f v| = 1 := by
  unfold realCharacter binarySign
  split_ifs <;> norm_num

theorem sum_realCharacter [Fintype V] (f : V →ₗ[𝔽₂] 𝔽₂) :
    ∑ v, realCharacter f v = if f = 0 then (Fintype.card V : ℝ) else 0 := by
  classical
  have h := sum_binarySign_linear f
  simp only [realCharacter]
  exact_mod_cast h

theorem uniform_character_expectation [Fintype V] (f : V →ₗ[𝔽₂] 𝔽₂) :
    finiteExpectation (uniformFiniteProbability V).weight (realCharacter f) =
      if f = 0 then 1 else 0 := by
  classical
  rw [uniformFiniteExpectation_eq, sum_realCharacter]
  by_cases hf : f = 0 <;> simp [hf, Fintype.card_ne_zero]

/-- The compatible affine event prescribed on an effective local dual space. -/
def effectiveEvent (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a v : V) : Prop :=
  ∀ s : S, s.val v = s.val a

/-- Evaluation of the displacement as a linear form on the effective space. -/
def displacementForm (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a v : V) :
    S →ₗ[𝔽₂] 𝔽₂ where
  toFun := fun s => s.val (v - a)
  map_add' := by intros; simp
  map_smul' := by intros; simp

theorem displacementForm_eq_zero_iff
    (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) (a v : V) :
    displacementForm S a v = 0 ↔ effectiveEvent S a v := by
  rw [LinearMap.ext_iff]
  simp [displacementForm, effectiveEvent, sub_eq_zero]

theorem effective_character_sum (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂))
    [Fintype S] (a v : V) :
    ∑ s : S, realCharacter s.val a * realCharacter s.val v =
      if effectiveEvent S a v then (Fintype.card S : ℝ) else 0 := by
  classical
  have h := sum_binarySign_linear (U := S) (displacementForm S a v)
  have hreal : (∑ s : S, (binarySign (displacementForm S a v s) : ℝ)) =
      if displacementForm S a v = 0 then (Fintype.card S : ℝ) else 0 := by
    exact_mod_cast h
  rw [displacementForm_eq_zero_iff] at hreal
  simpa only [displacementForm, LinearMap.coe_mk, AddHom.coe_mk, map_sub,
    binarySign_sub, Int.cast_mul, mul_comm, realCharacter] using hreal

theorem effective_indicator_expansion (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂))
    [Fintype S] (a v : V) :
    (if effectiveEvent S a v then (1 : ℝ) else 0) =
      (Fintype.card S : ℝ)⁻¹ *
        ∑ s : S, realCharacter s.val a * realCharacter s.val v := by
  classical
  rw [effective_character_sum]
  by_cases h : effectiveEvent S a v <;> simp [h, Fintype.card_ne_zero]

theorem effective_marginal [Fintype V]
    (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [Fintype S] (a : V) :
    finiteExpectation (uniformFiniteProbability V).weight
        (fun v => if effectiveEvent S a v then (1 : ℝ) else 0) =
      (Fintype.card S : ℝ)⁻¹ := by
  classical
  simp_rw [effective_indicator_expansion S a]
  rw [finiteExpectation_const_mul, finiteExpectation_sum]
  simp_rw [finiteExpectation_const_mul, uniform_character_expectation]
  simp

end PaperP1.Affine
