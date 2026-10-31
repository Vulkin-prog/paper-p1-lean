module

public import PaperP1.Affine.FourierBound

/-!
# The effective space of the rows of an affine system

Passing to the image of the transpose identifies row combinations that define
the same character. A compatible affine prescription is evaluation at any
solution, independently of the chosen representative of a row combination.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Algebra PaperP1.Probability

namespace PaperP1.Affine

local instance (P : Prop) : Decidable P := Classical.propDecidable P
local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V β : Type*} [AddCommGroup V] [Module 𝔽₂ V]
variable [Fintype β] [DecidableEq β]

def effectiveRowSpace (A : V →ₗ[𝔽₂] (β → 𝔽₂)) :
    Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂) := LinearMap.range (relationMap A)

omit [DecidableEq β] in
theorem effectiveRowEvent_iff (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (a v : V) :
    effectiveEvent (effectiveRowSpace A) a v ↔ A v = A a := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    apply dotProduct_eq_zero (A v - A a)
    intro u
    have he := h (⟨relationMap A u, LinearMap.mem_range_self _ u⟩ : effectiveRowSpace A)
    change dotProduct u (A v) = dotProduct u (A a) at he
    rw [dotProduct_comm, dotProduct_sub, he, sub_self]
  · intro h
    rintro ⟨f, ⟨u, rfl⟩⟩
    change dotProduct u (A v) = dotProduct u (A a)
    rw [h]

omit [DecidableEq β] in
theorem effectiveRowSign_independent_of_solution
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) {a a' : V} (h : A a = A a')
    (s : effectiveRowSpace A) : realCharacter s.val a = realCharacter s.val a' := by
  have he := (effectiveRowEvent_iff A a' a).mpr h s
  simp only [realCharacter, he]

omit [DecidableEq β] in
theorem affineIndicator_eq_effectiveIndicator
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) (a v : V) (ha : A a = b) :
    (if A v = b then (1 : ℝ) else 0) = effectiveIndicator (effectiveRowSpace A) a v := by
  simp only [effectiveIndicator, effectiveRowEvent_iff, ha]

/-- A local witness is chosen only from an explicit compatibility proof. -/
def affineWitness (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂)
    (h : Compatible A b) : V :=
  (Classical.choice ((compatible_iff_nonempty A b).mp h)).val

omit [Fintype β] [DecidableEq β] in
theorem affineWitness_solves (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂)
    (h : Compatible A b) : A (affineWitness A b h) = b :=
  (Classical.choice ((compatible_iff_nonempty A b).mp h)).property

omit [DecidableEq β] in
instance effectiveRowSpaceFintype (A : V →ₗ[𝔽₂] (β → 𝔽₂)) :
    Fintype (effectiveRowSpace A) :=
  Fintype.ofSurjective (relationMap A).rangeRestrict (by
    rintro ⟨f, ⟨u, hu⟩⟩
    exact ⟨u, Subtype.ext hu⟩)

variable [Fintype V]

theorem compatible_mass_eq_effectiveRate
    (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) (h : Compatible A b) :
    uniformSolutionMass A b = effectiveRate (effectiveRowSpace A) := by
  let a := affineWitness A b h
  have ha : A a = b := affineWitness_solves A b h
  calc
    uniformSolutionMass A b = finiteExpectation (uniformFiniteProbability V).weight
        (effectiveIndicator (effectiveRowSpace A) a) := by
      unfold uniformSolutionMass
      congr 1
      funext v
      by_cases hv : A v = b <;>
        simp only [effectiveIndicator, effectiveRowEvent_iff, ha, hv, ite_true, ite_false]
    _ = _ := effective_marginal (effectiveRowSpace A) a

omit [Fintype V] in
theorem effectiveRowSpace_card_pow (A : V →ₗ[𝔽₂] (β → 𝔽₂)) :
    Fintype.card (effectiveRowSpace A) = 2 ^ Module.finrank 𝔽₂ (effectiveRowSpace A) :=
  card_eq_two_pow_finrank (V := effectiveRowSpace A)

end PaperP1.Affine
