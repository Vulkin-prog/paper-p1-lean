module

public import PaperP1.Model.PrivateValueSystem
public import PaperP1.Probability.UniformLinearObservation

/-! # Joint raw-word observations and their actual independent uniform law

Surjectivity is an explicit finite matrix condition. No arithmetic pair
count is assumed or asserted by the observation identity.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawWordObservation

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem PaperP1.UniformFubini

variable {ι κ : Type*}

def joint (M : ℕ) (v : ι → ℕ) (t : κ → ℕ) :
    SampleSpace M →ₗ[F₂] ((ι → F₂) × (κ → F₂)) :=
  (valueSystem M v).prod (valueSystem M t)

theorem joint_apply (M : ℕ) (v : ι → ℕ) (t : κ → ℕ) (ω : SampleSpace M) :
    joint M v t ω = (valueSystem M v ω, valueSystem M t ω) := rfl

theorem independent_words {M : ℕ} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : ι → ℕ) (t : κ → ℕ) (hjoint : Function.Surjective (joint M v t))
    (f : (ι → F₂) × (κ → F₂) → ℝ) :
    average (fun ω ↦ f (valueSystem M v ω, valueSystem M t ω)) =
      average (fun u ↦ average (fun z ↦ f (u, z))) := by
  classical
  rw [← UniformFubini.product f]
  exact UniformLinearObservation.linear (joint M v t) hjoint f

end PaperP1.RawWordObservation
