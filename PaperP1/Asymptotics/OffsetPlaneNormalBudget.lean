module

public import PaperP1.Asymptotics.SmallNormalPlanes
public import PaperP1.Arithmetic.BoundedIntegerPlanes

/-! # Companion T20.4: actual planar support counts, small normals and O(B^5) planes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetPlaneNormalBudget

open Finset PaperP1.Arithmetic PaperP1.PrimitiveTripleDirection PaperP1.OffsetPlaneSupports
  PaperP1.OffsetLineCount PaperP1.BoundedIntegerPlanes

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem companion_T20_4 (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (family K (L + 1)).card ≤ (2 * K + 1) ^ 4 * (L + 1) ^ 5 ∧
      ∀ Y : ℝ, ((L + 1 : ℕ) : ℝ) ≤ Y → ∀ X : Fin 3 → ℕ,
      (∀ i, X i ∈ Ico N (2 * N)) →
      (∀ i, Module.finrank F₂ (squareClassSpace (X i) L) = L) →
      Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)) →
      ∀ A : Fin 3 → ℤ, Primitive A → ∀ h : ℤ,
        (((supports N L Y X A h).card : ℝ) ≤ sourceMajorant N L Y +
          4 * (((L + 1 : ℕ) : ℝ) ^ 2) / height A) ∧
        (δ * L ≤ (OffsetVertexCover.minimum (supports N L Y X A h) : ℝ) →
          (height A : ℝ) ≤ 16 * ((L + 1 : ℕ) : ℝ) / δ ∧
          |(h : ℝ)| ≤ 48 * (((L + 1 : ℕ) : ℝ) ^ 2) / δ ∧
          (A, h) ∈ family K (L + 1)) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (48 / δ)
  have hKpos : (0 : ℝ) < K := (div_pos (by norm_num : (0 : ℝ) < 48) hδ).trans hK
  have hKone : 1 ≤ K := by exact_mod_cast (show 0 < K by exact_mod_cast hKpos)
  have h16 : (16 / δ : ℝ) ≤ K :=
    (div_le_div_of_nonneg_right (by norm_num : (16 : ℝ) ≤ 48) hδ.le).trans hK.le
  refine ⟨K, hKone, ?_⟩
  intro C
  obtain ⟨NU, _hNU, hu⟩ := SmallNormalPlanes.uniform_bounds C δ hδ
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 10 (max NU NG), by omega, ?_⟩
  intro N hN L hband
  refine ⟨card_bound K (L + 1) (by omega), ?_⟩
  intro Y hYB X hX hrank hpair A hA h
  obtain ⟨_hNtwo, _hBmin, hBtwo, hthin, _hBlo, _hBhi⟩ := hg N (by omega) L hband
  have hLN : L + 1 ≤ N + 1 := by omega
  have hY : 1 < Y := lt_of_lt_of_le (by exact_mod_cast (show 1 < L + 1 by omega)) hYB
  have hinj := TwoPointSquareClasses.injective_evenMap_of_rank (X 0) L (hrank 0)
  have hdirect := hpair (by decide : (0 : Fin 3) ≠ 1)
  refine ⟨finite_count N L Y X A h (by omega) hLN hX hinj hdirect hYB hY hA, ?_⟩
  intro hcover
  obtain ⟨hnormal, hconstant⟩ := hu N (by omega) L hband Y hYB X hX hinj hdirect A hA h hcover
  refine ⟨hnormal, hconstant, (mem_family K (L + 1) A h).mpr ⟨?_, ?_⟩⟩
  · have hnormalK : (height A : ℝ) ≤ (K : ℝ) * ((L + 1 : ℕ) : ℝ) := by
      calc
        _ ≤ 16 * ((L + 1 : ℕ) : ℝ) / δ := hnormal
        _ = (16 / δ) * ((L + 1 : ℕ) : ℝ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h16 (Nat.cast_nonneg _)
    exact_mod_cast hnormalK
  · have hconstantK : (h.natAbs : ℝ) ≤ (K : ℝ) * (((L + 1 : ℕ) : ℝ) ^ 2) := by
      rw [← PlaneFibreBounds.abs_cast]
      calc
        _ ≤ 48 * (((L + 1 : ℕ) : ℝ) ^ 2) / δ := hconstant
        _ = (48 / δ) * (((L + 1 : ℕ) : ℝ) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hK.le (sq_nonneg _)
    exact_mod_cast hconstantK

end PaperP1.OffsetPlaneNormalBudget
