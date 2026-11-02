module

public import PaperP1.Arithmetic.OffsetPlaneSupports
public import PaperP1.Asymptotics.OffsetLineMajorant
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # A macroscopic vertex cover forces a uniformly small primitive normal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallNormalPlanes

open Finset PaperP1.Arithmetic PaperP1.TripleCross PaperP1.PrimitiveTripleDirection
  PaperP1.OffsetPlaneSupports PaperP1.OffsetLineCount PaperP1.OffsetLineMajorant

theorem height_from_count {L : ℕ} (hL : 1 ≤ L) (A : Fin 3 → ℤ) (hA : Primitive A)
    (δ m M : ℝ) (hδ : 0 < δ) (hlower : δ * L ≤ m) (hsmall : M ≤ δ * L / 2)
    (hcount : m ≤ M + 4 * (((L + 1 : ℕ) : ℝ) ^ 2) / height A) :
    (height A : ℝ) ≤ 16 * ((L + 1 : ℕ) : ℝ) / δ := by
  have hAp : (0 : ℝ) < height A := by exact_mod_cast height_pos A hA
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hB : ((L + 1 : ℕ) : ℝ) ≤ 2 * L := by exact_mod_cast (show L + 1 ≤ 2 * L by omega)
  have hhalf : δ * L / 2 ≤ 4 * (((L + 1 : ℕ) : ℝ) ^ 2) / height A :=
    by linarith only [hlower, hsmall, hcount]
  have hmul := (le_div_iff₀ hAp).mp hhalf
  have hprod : δ * L * height A ≤ 8 * (((L + 1 : ℕ) : ℝ) ^ 2) := by nlinarith only [hmul]
  have hmid : 8 * (((L + 1 : ℕ) : ℝ) ^ 2) ≤ 16 * ((L + 1 : ℕ) : ℝ) * L := by
    have hh := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 8 * ((L + 1 : ℕ) : ℝ))
    nlinarith only [hh]
  apply (le_div_iff₀ hδ).mpr
  by_contra hnot
  have hstrict : 16 * ((L + 1 : ℕ) : ℝ) < (height A : ℝ) * δ := lt_of_not_ge hnot
  have hmult := mul_lt_mul_of_pos_right hstrict hLp
  nlinarith only [hmult, hprod, hmid]

theorem uniform_bounds (C δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ Y : ℝ, ((L + 1 : ℕ) : ℝ) ≤ Y →
      ∀ X : Fin 3 → ℕ, (∀ i, X i ∈ Ico N (2 * N)) →
      Function.Injective (evenSquareClassMap (X 0) L) →
      Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L) →
      ∀ A : Fin 3 → ℤ, Primitive A → ∀ h : ℤ,
      δ * L ≤ (OffsetVertexCover.minimum (supports N L Y X A h) : ℝ) →
        (height A : ℝ) ≤ 16 * ((L + 1 : ℕ) : ℝ) / δ ∧
          |(h : ℝ)| ≤ 48 * (((L + 1 : ℕ) : ℝ) ^ 2) / δ := by
  obtain ⟨NM, hm⟩ := majorant_little_o_uniform C (δ / 4) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 10 (max NM NG), by omega, ?_⟩
  intro N hN L hband Y hYB X hX hinj hdirect A hA h hcover
  obtain ⟨_hNtwo, _hBmin, hBtwo, hthin, _hBlo, _hBhi⟩ := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  have hLN : L + 1 ≤ N + 1 := by omega
  have hY : 1 < Y := lt_of_lt_of_le (by exact_mod_cast (show 1 < L + 1 by omega)) hYB
  have hBR : ((L + 1 : ℕ) : ℝ) ≤ 2 * L := by exact_mod_cast (show L + 1 ≤ 2 * L by omega)
  have hmajor := hm N (by omega) L hband Y hYB
  have hsmall : sourceMajorant N L Y ≤ δ * L / 2 := by
    have hh := mul_le_mul_of_nonneg_left hBR hδ.le
    nlinarith only [hmajor, hh]
  have hcard : δ * L ≤ ((supports N L Y X A h).card : ℝ) :=
    hcover.trans (by exact_mod_cast OffsetVertexCover.minimum_le_supports (supports N L Y X A h))
  have hcount := finite_count N L Y X A h (by omega) hLN hX hinj hdirect hYB hY hA
  have hnormal := height_from_count hL A hA δ _ _ hδ hcard hsmall hcount
  refine ⟨hnormal, ?_⟩
  have hpos : (0 : ℝ) < (supports N L Y X A h).card := lt_of_lt_of_le
    (mul_pos hδ (by exact_mod_cast (show 0 < L by omega))) hcard
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < (supports N L Y X A h).card by exact_mod_cast hpos)
  have hdot := dot_natAbs_le A u (height A) (L + 1) (coordinate_natAbs_le_height A)
    (coordinate_bound N L Y X A h u hu)
  rw [on_plane N L Y X A h u hu, Int.natAbs_neg] at hdot
  have hconstant : |(h : ℝ)| ≤ 3 * (height A : ℝ) * ((L + 1 : ℕ) : ℝ) := by
    rw [PlaneFibreBounds.abs_cast]
    exact_mod_cast hdot
  calc
    _ ≤ 3 * (height A : ℝ) * ((L + 1 : ℕ) : ℝ) := hconstant
    _ ≤ 3 * (16 * ((L + 1 : ℕ) : ℝ) / δ) * ((L + 1 : ℕ) : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right hnormal (by positivity : (0 : ℝ) ≤ 3 * ((L + 1 : ℕ) : ℝ))
      nlinarith only [hh]
    _ = _ := by ring

end PaperP1.SmallNormalPlanes
