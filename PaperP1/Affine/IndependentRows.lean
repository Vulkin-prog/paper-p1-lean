module

public import PaperP1.Affine.EffectiveRows

/-!
# Independent binary rows have the exact uniform output law

With no row relations, the signed Fourier sum consists only of the zero
word. Every prescribed output therefore has probability exactly 2^(-m).
This derives all output probabilities without assuming affine compatibility.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

open PaperP1.Probability PaperP1.Algebra Finset

local instance independentRowsPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V β : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V]
variable [Fintype β] [DecidableEq β]

omit [Fintype V] [DecidableEq β] in
theorem relationMap_injective_of_full_effective_rank
    (A : V →ₗ[𝔽₂] (β → 𝔽₂))
    (hrank : Module.finrank 𝔽₂ (effectiveRowSpace A) = Fintype.card β) :
    Function.Injective (relationMap A) := by
  have h := (relationMap A).finrank_range_add_finrank_ker
  change Module.finrank 𝔽₂ (effectiveRowSpace A) +
    Module.finrank 𝔽₂ (LinearMap.ker (relationMap A)) = _ at h
  rw [hrank, Module.finrank_fintype_fun_eq_card] at h
  have hker : Module.finrank 𝔽₂ (LinearMap.ker (relationMap A)) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)

omit [Fintype V] in
theorem relationSignedSum_eq_one_of_injective (A : V →ₗ[𝔽₂] (β → 𝔽₂))
    (hinj : Function.Injective (relationMap A)) (b : β → 𝔽₂) :
    relationSignedSum A b = 1 := by
  classical
  unfold relationSignedSum
  rw [Finset.sum_eq_single 0]
  · rw [map_zero]
    simp [binarySign, dotProduct]
  · intro u _ hu
    have hrel : relationMap A u ≠ 0 := by
      intro h
      exact hu (hinj (h.trans (map_zero _).symm))
    simp only [hrel, ite_false]
  · simp

theorem uniformSolutionMass_of_injective_relationMap (A : V →ₗ[𝔽₂] (β → 𝔽₂))
    (hinj : Function.Injective (relationMap A)) (b : β → 𝔽₂) :
    uniformSolutionMass A b = (Fintype.card (β → 𝔽₂) : ℝ)⁻¹ := by
  classical
  have hid := affineFiber_fourier_identity A b
  rw [relationSignedSum_eq_one_of_injective A hinj b, mul_one] at hid
  have hr : (Fintype.card (β → 𝔽₂) : ℝ) *
      ((Finset.univ.filter fun x : V ↦ A x = b).card : ℝ) = Fintype.card V := by
    exact_mod_cast hid
  have hmass : uniformSolutionMass A b =
      ((Finset.univ.filter fun x : V ↦ A x = b).card : ℝ) / Fintype.card V := by
    rw [uniformSolutionMass_eq_card_ratio]
    congr 1
    apply congrArg (fun n : ℕ ↦ (n : ℝ))
    refine @Fintype.card_of_subtype V (fun x : V ↦ x ∈ solutionSet A b)
      (Finset.univ.filter fun x : V ↦ A x = b) ?_ (realSolutionFintype A b)
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_solutionSet_iff]
  rw [hmass]
  have hV : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hW : (Fintype.card (β → 𝔽₂) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hV, hW]
  nlinarith

/-- Every output word has its fair-cube mass; no output is ruled out. -/
theorem uniformSolutionMass_of_full_effective_rank (A : V →ₗ[𝔽₂] (β → 𝔽₂))
    (hrank : Module.finrank 𝔽₂ (effectiveRowSpace A) = Fintype.card β) (b : β → 𝔽₂) :
    uniformSolutionMass A b = (2 ^ Fintype.card β : ℝ)⁻¹ := by
  have h := uniformSolutionMass_of_injective_relationMap A
    (relationMap_injective_of_full_effective_rank A hrank) b
  simpa only [Fintype.card_fun, ZMod.card, Nat.cast_pow, Nat.cast_ofNat] using h

end PaperP1.Affine
