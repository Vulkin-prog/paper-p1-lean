module

public import PaperP1.Asymptotics.SmallTransverseHostCount

/-! # The simultaneous small-component exceptional set has actual mass N^(-1+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallTransverseMassUnderInputs

open Finset PaperP1.Model PaperP1.ManyPlanarSquareProducts

theorem uniform_bound (C : ℝ) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ (UniformOrdinarySurfaceCover.UniformCover k 4 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k + 3) M) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
        ∀ S : Finset (Fin 3 → ℕ),
          (∀ X ∈ S, RegularDirect N L X ∧ SmallTransverseHostData.Many (24 * k) L H X) →
          (S.card : ℝ) ≤ (N : ℝ) ^ (1 + ε) ∧ mass L S ≤ (N : ℝ) ^ (-1 + ε) ∧
            primitiveMass L S ≤ (N : ℝ) ^ (-1 + ε)) := by
  obtain ⟨k, hk, hp⟩ := SmallTransverseHostCount.uniform_count C D (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (((2 : ℝ) ^ C) ^ 2)
    (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨k, hk, ?_⟩
  intro hCover hCurve
  obtain ⟨NC, _hNC, hc⟩ := hp hCover hCurve
  refine ⟨10 + NG + NF + NC, by omega, ?_⟩
  intro N hN L H hband hH S hS
  have hgeom := hg N (by omega) L hband
  have hcount := hc N (by omega) L H hband hH S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmass : mass L S ≤ (N : ℝ) ^ (-1 + ε) := by
    calc
      _ ≤ (S.card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 := mass_le (by omega)
        (by have hh := hgeom.2.2.1; omega) S (fun X hX ↦ (hS X hX).1)
      _ ≤ (N : ℝ) ^ (1 + ε / 2) * ((((2 : ℝ) ^ C) ^ 2) * (N : ℝ) ^ (-2 : ℝ)) :=
        mul_le_mul hcount (CriticalChannelPowers.nominal_square_upper (by omega) hband)
          (sq_nonneg _) (Real.rpow_nonneg hn.le _)
      _ = (((2 : ℝ) ^ C) ^ 2) * (N : ℝ) ^ (-1 + ε / 2) := by
        rw [← mul_assoc, mul_comm ((N : ℝ) ^ (1 + ε / 2)), mul_assoc, ← Real.rpow_add hn]
        congr 2
        ring
      _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
      _ = _ := by congr 1; ring
  refine ⟨hcount.trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)), hmass, (primitive_mass_le L S).trans hmass⟩

def exceptional (N L H k : ℕ) : Finset (Fin 3 → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin 3 ↦ dyadicBlock N)).filter (fun X ↦
    RegularDirect N L X ∧ TripleProbabilityBound.Primitive L X ∧
      SmallTransverseHostData.Many (24 * k) L H X)

theorem exceptional_data {N L H k : ℕ} {X : Fin 3 → ℕ} (hX : X ∈ exceptional N L H k) :
    RegularDirect N L X ∧ TripleProbabilityBound.Primitive L X ∧
      SmallTransverseHostData.Many (24 * k) L H X := by
  classical
  exact (mem_filter.mp hX).2

theorem outside_small_count {N L H k : ℕ} (hN : 2 ≤ N) (hH : L + 1 ≤ H)
    (X : Fin 3 → ℕ) (hX : RegularDirect N L X) (hprim : TripleProbabilityBound.Primitive L X)
    (hnot : X ∉ exceptional N L H k) (D : Finset (TransverseMotifs.Vertex L))
    (hD : CoverGraphResolution.IsCover (ThreeBlockCoordinates.rows X L H) D) :
    ComponentSixVertexBudget.smallCount X L H D < 24 * k := by
  classical
  by_contra hn
  have hX2 (i : Fin 3) : 2 ≤ X i := hN.trans (mem_Ico.mp (hX.2.1 i).1).1
  have hm := SmallTransverseHostData.many_of_cover hX2 hH D hD (Nat.le_of_not_gt hn)
  apply hnot
  apply mem_filter.mpr
  exact ⟨Fintype.mem_piFinset.mpr (fun i ↦ (hX.2.1 i).1), hX, hprim, hm⟩

end PaperP1.SmallTransverseMassUnderInputs
