module

public import PaperP1.Arithmetic.EvenIndependentValues
public import PaperP1.Model.PrivateValuePrescriptions

/-! # Arbitrary relative value bits are realizable from injectivity on even selections alone -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenValuePrescriptions

open Finset PaperP1.Arithmetic PaperP1.Model.InfiniteRademacher PaperP1.FiniteEvenSquareClasses
  PaperP1.PrivateValuePrescriptions

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem prescribe_relative_to (S : Finset ℕ) (hS : EvenIndependentValues.Independent S)
    (b : S → F₂) (a : S) :
    ∃ ω : InfiniteSample, ∀ n : S, infiniteValueBit ω n.val - infiniteValueBit ω a.val = b n - b a := by
  classical
  let f := EvenImage.evenMap (K := F₂) (data S)
  have hfi : Function.Injective f := hS
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hfi)
  let h : (ℕ →₀ F₂) →ₗ[F₂] F₂ := (evaluation S b).comp ((LinearMap.ker (EvenSupportRank.sumMap F₂ S)).subtype.comp g)
  refine ⟨sampleOf h, fun n ↦ ?_⟩
  let w : LinearMap.ker (EvenSupportRank.sumMap F₂ S) :=
    ⟨Pi.single n 1 - Pi.single a 1, by
      simp only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply, Pi.sub_apply, sum_sub_distrib,
        Fintype.sum_pi_single', sub_self]⟩
  have hfw : f w = parityVec n.val - parityVec a.val := by
    change EvenImage.combination (K := F₂) (data S) (Pi.single n 1 - Pi.single a 1) = _
    rw [map_sub]
    simp only [EvenImage.combination, Fintype.linearCombination_apply_single, one_smul, data]
  have hgw : g (parityVec n.val - parityVec a.val) = w := by
    rw [← hfw]
    exact congrArg (fun q : LinearMap.ker (EvenSupportRank.sumMap F₂ S) →ₗ[F₂]
      LinearMap.ker (EvenSupportRank.sumMap F₂ S) ↦ q w) hg
  rw [value_of_functional, value_of_functional, ← map_sub]
  change evaluation S b (g (parityVec n.val - parityVec a.val)).val = _
  rw [hgw]
  change evaluation S b (Pi.single n 1 - Pi.single a 1) = _
  rw [map_sub, evaluation_single, evaluation_single]

theorem prescribe_up_to_constant (S : Finset ℕ) (hS : EvenIndependentValues.Independent S) (b : S → F₂) :
    ∃ (ω : InfiniteSample) (δ : F₂), ∀ n : S, infiniteValueBit ω n.val = b n + δ := by
  classical
  by_cases hne : S.Nonempty
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨ω, hω⟩ := prescribe_relative_to S hS b ⟨a, ha⟩
    refine ⟨ω, infiniteValueBit ω a - b ⟨a, ha⟩, fun n ↦ ?_⟩
    calc
      _ = (infiniteValueBit ω n.val - infiniteValueBit ω a) + infiniteValueBit ω a := by abel
      _ = (b n - b ⟨a, ha⟩) + infiniteValueBit ω a := by rw [hω n]
      _ = _ := by abel
  · refine ⟨fun _ ↦ 0, 0, fun n ↦ False.elim (hne ⟨n.val, n.property⟩)⟩

end PaperP1.EvenValuePrescriptions
