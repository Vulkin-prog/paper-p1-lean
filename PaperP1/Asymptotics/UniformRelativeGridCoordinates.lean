module

public import PaperP1.Asymptotics.UniformRelativeIntervalCoordinates

/-! # Uniform reduced coordinates for arbitrary image radius on a relative grid -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformRelativeGridCoordinates

open PaperP1.RelativeIntervalLattice PaperP1.RelativeIntervalLatticeHeight
open PaperP1.DeterminantRelativeIntervals PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction
open PaperP1.BinaryLatticeCoordinateBounds

theorem uniform_grid_coordinates (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ κ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 1 ≤ M → M ≤ N →
      ∀ D E : ℝ, 1 ≤ D → 1 ≤ E → D ≤ (Q : ℝ) * N → E ≤ (Q : ℝ) * N →
      ∀ k : ℕ, k ≤ 2 * M → ∀ R : ℝ, 0 ≤ R →
      let T := transform D E M (intervalCenter M D E k)
      ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ : ℝ,
        L₀ = sideLength R (squareNorm (realImage T (fun i ↦ A i 0))) ∧
        L₁ = sideLength R (squareNorm (realImage T (fun i ↦ A i 1))) ∧
        A * B = 1 ∧ B * A = 1 ∧ A.det = 1 ∧
        (∀ i j, |A i j| ≤ ((N ^ κ : ℕ) : ℤ)) ∧ (∀ i j, |B i j| ≤ ((N ^ κ : ℕ) : ℤ)) ∧
        (∀ w : Fin 2 → ℤ, w ≠ 0 →
          squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T w)) ∧
        0 ≤ L₁ ∧ L₁ ≤ L₀ ∧ L₀ * L₁ ≤ 4 * R ^ 2 * (D * E) / M ∧
        L₀ ≤ 2 * R * (((2 * (N ^ 2) ^ 2 : ℕ) : ℝ) + 1) ∧
        R ^ 2 * (D * E) / M ≤ L₀ ^ 2 ∧
        ∀ z : Fin 2 → ℤ, (∀ i, |realImage T z i| ≤ R) →
          |(B.mulVec z 0 : ℝ)| ≤ L₀ ∧ |(B.mulVec z 1 : ℝ)| ≤ L₁ := by
  obtain ⟨κ, N₁, hboxes⟩ := UniformLatticeCoordinateBoxes.uniform_coordinate_boxes 2
  obtain ⟨N₂, hheight⟩ := uniform_power_heights Q hQ
  refine ⟨κ, max N₁ N₂, ?_⟩
  intro N hN M hM hMN D E hD hE hDN hEN k hk R hR
  have hDp : 0 < D := by linarith
  have hEp : 0 < E := by linarith
  have hMp : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMp
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMNR : (M : ℝ) ≤ N := by exact_mod_cast hMN
  let T := transform D E M (intervalCenter M D E k)
  let S := inverse D E M (intervalCenter M D E k)
  have hcenter := interval_center_range M k hMp hk D E hDp hEp
  have hentries := hheight N (by omega) D E M (intervalCenter M D E k)
    hD hE hM1 hMNR hDN hEN hcenter.1 hcenter.2
  have hST : S * T = 1 := (inverse_products D E M _ hDp.ne' hEp.ne' hMR.ne').2
  obtain ⟨A, B, L₀, L₁, hL₀, hL₁, hAB, hBA, hdet, hA, hB, hmin,
    hnonnegative, horder, hproduct, hupper, hlower, hpoints⟩ :=
      hboxes N (by omega) T S hST hentries.1 hentries.2 R hR
  have hdetT : T.det = (M : ℝ) / (D * E) := determinant D E M _
  have habs : |T.det| = (M : ℝ) / (D * E) := by rw [hdetT, abs_of_pos (div_pos hMR (mul_pos hDp hEp))]
  have hproduct' : L₀ * L₁ ≤ 4 * R ^ 2 * (D * E) / M := by
    calc
      _ ≤ 4 * R ^ 2 / |T.det| := hproduct
      _ = _ := by rw [habs]; field_simp
  have hlower' : R ^ 2 ≤ L₀ ^ 2 * ((M : ℝ) / (D * E)) := by simpa only [habs] using hlower
  have hscale : R ^ 2 * (D * E) / M ≤ L₀ ^ 2 := by
    apply (div_le_iff₀ hMR).mpr
    apply (le_div_iff₀ (mul_pos hDp hEp)).mp
    simpa only [mul_div_assoc] using hlower'
  exact ⟨A, B, L₀, L₁, hL₀, hL₁, hAB, hBA, hdet, hA, hB, hmin,
    hnonnegative, horder, hproduct', hupper, hscale, hpoints⟩

end PaperP1.UniformRelativeGridCoordinates
