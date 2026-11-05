module

public import PaperP1.Asymptotics.PrimitiveTripleMass
public import PaperP1.Asymptotics.ManyPlanarSquareProducts
public import PaperP1.Combinatorics.FamilyEnumerationWeights

/-! # The full ordered primitive triple activity has power three halves

Each unordered support has at most six injective enumerations. The complete
internal primitive mass bound therefore controls every ordered subpopulation,
including the original small-component exceptional sets.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveTripleTupleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_activity (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ S : Finset (Fin 3 → ℕ),
      (∀ X ∈ S, Function.Injective X ∧ (∀ i, X i ∈ dyadicBlock N) ∧ TripleProbabilityBound.Primitive L X) →
      (∑ X ∈ S, (infiniteJointMoment L (TripleProbabilityBound.tupleSet X) +
        |infiniteCenteredCoefficient L (TripleProbabilityBound.tupleSet X)|)) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  classical
  obtain ⟨NM, _hNM, hm⟩ := PrimitiveTripleMass.uniform_actual_activity C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 6 (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NM + NF, by omega, ?_⟩
  intro N hN L hband S hS
  let F := S.image TripleProbabilityBound.tupleSet
  have hF : ∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ ConnectedWindowFamilies.Primitive L I := by
    intro I hI
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hI
    have hd := hS X hX
    refine ⟨?_, ?_, hd.2.2⟩
    · intro x hx
      obtain ⟨i, _hi, rfl⟩ := mem_image.mp hx
      exact hd.2.1 i
    · rw [TripleProbabilityBound.tupleSet, card_image_of_injective _ hd.1, card_univ, Fintype.card_fin]
  let w := fun I : Finset ℕ ↦ infiniteJointMoment L I + |infiniteCenteredCoefficient L I|
  have hfinite := FamilyEnumerationWeights.weighted_bound F S w
    (fun I ↦ add_nonneg (infiniteJointMoment_nonneg L I) (abs_nonneg _))
    (fun I hI ↦ (hF I hI).2.1) (by
      intro X hX
      exact ⟨(hS X hX).1, mem_image.mpr ⟨X, hX, rfl⟩⟩)
  norm_num only [Nat.factorial, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] at hfinite
  have hmass : (∑ I ∈ F, w I) ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    exact hm N (by omega) L hband F hF
  calc
    _ ≤ 6 * ∑ I ∈ F, w I := hfinite
    _ ≤ 6 * (N : ℝ) ^ (-3 / 2 + ε / 2) := mul_le_mul_of_nonneg_left hmass (by norm_num)
    _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ S : Finset (Fin 3 → ℕ),
      (∀ X ∈ S, Function.Injective X ∧ (∀ i, X i ∈ dyadicBlock N) ∧ TripleProbabilityBound.Primitive L X) →
      ManyPlanarSquareProducts.mass L S ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨N₀, hN₀, hm⟩ := uniform_activity C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband S hS
  exact (sum_le_sum fun X _ ↦ le_add_of_nonneg_right
    (abs_nonneg (infiniteCenteredCoefficient L (TripleProbabilityBound.tupleSet X)))).trans
      (hm N hN L hband S hS)

end PaperP1.PrimitiveTripleTupleMass
