module

public import PaperP1.Probability.MeasureFiniteLaw
public import PaperP1.Probability.BinaryForcingFlip

/-! # Exact finite observation of arbitrary auxiliary orientation randomness

The table records the orientation at every source and every possible raw
source word. Its law is the actual pushforward, with measurability explicit.
No uniformity or approximation of the auxiliary probability is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteOrientationObservation

open MeasureTheory PaperP1.Arithmetic PaperP1.Probability PaperP1.Algebra

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

structure Table (ι κ : Type*) where
  value : ι → κ → F₂


instance : Fintype (Table ι κ) := by
  classical
  exact Fintype.ofEquiv (ι → κ → F₂) ⟨(fun f ↦ ⟨f⟩), Table.value, (fun _ ↦ rfl), (fun _ ↦ rfl)⟩

instance : MeasurableSpace (Table ι κ) := ⊤

instance : MeasurableSingletonClass (Table ι κ) := ⟨fun _ ↦ trivial⟩

variable {Ξ : Type*} [MeasurableSpace Ξ]

def encode (g : ι → κ → Ξ → F₂) (ξ : Ξ) : Table ι κ := ⟨fun j u ↦ g j u ξ⟩

theorem encode_measurable (g : ι → κ → Ξ → F₂)
    (hg : ∀ j u s, MeasurableSet {ξ : Ξ | g j u ξ = s}) : Measurable (encode g) := by
  apply measurable_to_countable'
  intro t
  have he : (encode g) ⁻¹' {t} = ⋂ j, ⋂ u, {ξ : Ξ | g j u ξ = t.value j u} := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h j u
      exact congrArg (fun z : Table ι κ ↦ z.value j u) h
    · intro h
      cases t
      change Table.mk _ = Table.mk _
      congr 1
      funext j u
      exact h j u
  rw [he]
  exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun u ↦ hg j u (t.value j u)

def law (μ : Measure Ξ) [IsProbabilityMeasure μ] (g : ι → κ → Ξ → F₂)
    (hg : Measurable (encode g)) : FiniteProbability (Table ι κ) :=
  finiteObservationProbability μ (encode g) hg

theorem expectation_eq (μ : Measure Ξ) [IsProbabilityMeasure μ] (g : ι → κ → Ξ → F₂)
    (hg : Measurable (encode g)) (f : Table ι κ → ℝ) :
    finiteExpectation (law μ g hg).weight f = ∫ ξ, f (encode g ξ) ∂μ :=
  finiteObservation_expectation μ (encode g) hg f

theorem coordinate_expectation (μ : Measure Ξ) [IsProbabilityMeasure μ] (g : ι → κ → Ξ → F₂)
    (hg : Measurable (encode g)) (j : ι) (u : κ) (f : F₂ → ℝ) :
    finiteExpectation (law μ g hg).weight (fun t ↦ f (t.value j u)) = ∫ ξ, f (g j u ξ) ∂μ :=
  expectation_eq μ g hg (fun t ↦ f (t.value j u))

theorem weight_eq (μ : Measure Ξ) [IsProbabilityMeasure μ] (g : ι → κ → Ξ → F₂)
    (hg : Measurable (encode g)) (t : Table ι κ) :
    (law μ g hg).weight t = μ.real ((encode g) ⁻¹' {t}) :=
  finiteObservationProbability_weight μ (encode g) hg t

end PaperP1.FiniteOrientationObservation
