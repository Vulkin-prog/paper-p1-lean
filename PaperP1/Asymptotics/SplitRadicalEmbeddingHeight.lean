module

public import PaperP1.Algebra.SplitRadicalEmbeddingHeight
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # One threshold gives the actual source-coordinate height for every polynomial-height split system -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformSplitRadicalEmbeddingHeight

open PaperP1.SplitRadicalPointHeight PaperP1.SplitRadicalEmbeddingHeight

theorem uniform_height {ι : Type*} [Fintype ι] (K D : ℕ) (A b r : ℝ)
    (hdegree : A + (K : ℝ) ≤ 2 * D) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ I J : ι → Finset ℤ, ∀ c w : ι → ℤ, ∀ x y : ℤ,
      x.natAbs ≤ 2 * N → y.natAbs ≤ 2 * N →
      (∀ i, ∀ a ∈ I i, (a.natAbs : ℝ) ≤ b * (Real.log N) ^ r) →
      (∀ i, ∀ a ∈ J i, (a.natAbs : ℝ) ≤ b * (Real.log N) ^ r) →
      (∀ i, (I i).card + (J i).card ≤ K) →
      (∀ i, ((c i).natAbs : ℝ) ≤ (N : ℝ) ^ A) →
      (∀ i, w i ^ 2 = c i * integerProduct (I i) x * integerProduct (J i) y) →
      (∀ a d : ℕ, a + d ≤ D → ((x ^ a * y ^ d).natAbs : ℝ) ≤
        commonConstant (Fintype.card ι) K D * (N : ℝ) ^ D) ∧
      (∀ i, ((w i).natAbs : ℝ) ≤ commonConstant (Fintype.card ι) K D * (N : ℝ) ^ D) ∧
      ((∑ i, w i).natAbs : ℝ) ≤ commonConstant (Fintype.card ι) K D * (N : ℝ) ^ D := by
  obtain ⟨Nlog, hNlog⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow b r 1 (by norm_num)
  refine ⟨max 1 Nlog, ?_⟩
  intro N hN I J c w x y hx hy hI hJ hK hc heq
  have hoff : b * (Real.log N) ^ r ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using hNlog N (by omega)
  apply coordinates_height I J c w x y N K D A (by omega) hx hy
  · intro i a ha
    exact_mod_cast (hI i a ha).trans hoff
  · intro i a ha
    exact_mod_cast (hJ i a ha).trans hoff
  · exact hK
  · exact hdegree
  · exact hc
  · exact heq

end PaperP1.UniformSplitRadicalEmbeddingHeight
