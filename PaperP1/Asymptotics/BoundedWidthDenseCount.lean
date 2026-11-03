module

public import PaperP1.Asymptotics.OneTargetLogDenseCount
public import PaperP1.Arithmetic.BoundedWidthWindows
public import PaperP1.Arithmetic.UniformFixedSourceCertificates

/-! # Every actual bounded-width block with a dense prescribed-space intersection has subpower many centers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedWidthDenseCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.CriticalBandScale
  PaperP1.BoundedWidthWindows

local instance boundedWidthDensePrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance intersectionAddCommGroup (W Y : Submodule F₂ (ℕ →₀ F₂)) : AddCommGroup ↥(W ⊓ Y) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ℕ →₀ F₂) (W ⊓ Y)

theorem uniform_count (s D : ℕ) (hD : 1 ≤ D) (a b C η ε : ℝ)
    (ha : 0 < a) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ U : ℕ → Finset ℕ, ∀ S : Finset ℕ,
        (∀ X ∈ S, a * N ≤ X ∧ (X : ℝ) ≤ b * N ∧
          (∀ n ∈ U X, ((n : ℤ) - X).natAbs ≤ D * (L + 1)) ∧
          η * L ≤ (Module.finrank F₂ ↥(W ⊓ FiniteEvenSquareClasses.space (U X)) : ℝ)) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  let A := ((2 * D + 1 : ℕ) : ℝ) * upperScale
  let ξ := η / (4 * (D : ℝ))
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) upperScale_pos.le
  have hξ : 0 < ξ := div_pos hη (by positivity)
  obtain ⟨L₀, _hL₀, Nc, _hNc, hc⟩ := OneTargetLogDenseCount.uniform_count s (a / 2) (b + 1) A ξ ε
    (by positivity) hA hξ hε
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C (L₀ + 1)
  obtain ⟨Nw, hw⟩ := UniformFixedSourceCertificates.logarithmic_width_le_nat_eventually A hA
  obtain ⟨Nt, ht⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    ((8 * (D : ℝ) / a) * upperScale) 1 1 (by norm_num)
  refine ⟨max 3 (max Nc (max Ng (max Nw Nt))), by omega, ?_⟩
  intro N hN L hband x hx W hW U S hS
  let : FiniteDimensional F₂ W := TwoTargetRegularization.source_finite x L W hW
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  have hB := hgeom.2.2.2.2.2
  let R := D * (L + 1)
  let H := 2 * R
  have hRpos : 1 ≤ R := by dsimp [R]; nlinarith only [Nat.mul_le_mul_right (L + 1) hD]
  have hLH : L ≤ H := by dsimp [H, R]; nlinarith only [Nat.mul_le_mul_right (L + 1) hD]
  have hHwidth : ((H + 1 : ℕ) : ℝ) ≤ A * Real.log N := by
    have hfirst : ((H + 1 : ℕ) : ℝ) ≤ ((2 * D + 1 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) := by
      dsimp [H, R]
      push_cast
      nlinarith only [Nat.cast_nonneg (α := ℝ) L]
    exact hfirst.trans (by
      simpa only [A, mul_assoc] using mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg (2 * D + 1)))
  have hHN : H ≤ N := hw N (by omega) H hHwidth
  have hthin : 8 * (R : ℝ) ≤ a * N := by
    have ht' := ht N (by omega)
    simp only [Real.rpow_one] at ht'
    have h := mul_le_mul_of_nonneg_left ht' ha.le
    have heq : a * (((8 * (D : ℝ) / a) * upperScale) * Real.log N) =
        (8 * (D : ℝ)) * (upperScale * Real.log N) := by field_simp
    rw [heq] at h
    have hmul := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 8 * D)
    dsimp [R]
    push_cast
    push_cast at hmul
    nlinarith only [h, hmul]
  have hshift (X : ℕ) (hX : X ∈ S) : R ≤ X ∧ 2 ≤ center X R ∧
      (a / 2) * N ≤ center X R ∧ ((center X R : ℕ) : ℝ) ≤ (b + 1) * N := by
    have hXlo := (hS X hX).1
    have hXhi := (hS X hX).2.1
    have h8X : 8 * R ≤ X := by exact_mod_cast hthin.trans hXlo
    have hRX : R ≤ X := by omega
    have hcenter : ((center X R : ℕ) : ℝ) = (X : ℝ) - R + 1 := by
      unfold center
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hRX]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    exact ⟨hRX, by unfold center; omega, by linarith only [hcenter, hXlo, hthin],
      by linarith only [hcenter, hXhi, Nat.cast_nonneg (α := ℝ) R, hN1]⟩
  have hξH : ξ * H ≤ η * L := by
    have hHle : (H : ℝ) ≤ 4 * (D : ℝ) * L := by
      dsimp [H, R]
      push_cast
      have hLL : (L : ℝ) + 1 ≤ 2 * L := by exact_mod_cast (show L + 1 ≤ 2 * L by omega)
      nlinarith only [mul_le_mul_of_nonneg_left hLL hDpos.le]
    calc
      _ ≤ ξ * (4 * (D : ℝ) * L) := mul_le_mul_of_nonneg_left hHle hξ.le
      _ = _ := by dsimp [ξ]; field_simp
  have hxpos : ∀ i, 2 ≤ x i := by intro i; have h := (mem_Ico.mp (hx i)).1; omega
  have hWlong : W ≤ ⨆ i, squareClassSpace (x i) H :=
    hW.trans (iSup_mono fun i ↦ window_space_mono (by have h := hxpos i; omega) hLH)
  have hcount := hc N (by omega) H (by have h := hgeom.2.1; omega) hHwidth x hxpos
    (fun i ↦ FixedSourceCertificate.sourceValues_le_square x (by omega) hHN hx i) W hWlong
    (S.image fun X ↦ center X R) (by
      intro y hy
      obtain ⟨X, hX, rfl⟩ := mem_image.mp hy
      have hsh := hshift X hX
      have hspace := space_le_window (U X) X R hsh.1 (hS X hX).2.2.1
      have hmono := Submodule.finrank_mono (inf_le_inf_left W hspace)
      have hr : (Module.finrank F₂ ↥(W ⊓ FiniteEvenSquareClasses.space (U X)) : ℝ) ≤
          Module.finrank F₂ ↥(W ⊓ squareClassSpace (center X R) H) := by exact_mod_cast hmono
      exact ⟨hsh.2.1, hsh.2.2.1, hsh.2.2.2, hξH.trans ((hS X hX).2.2.2.trans hr)⟩)
  simpa only [card_image_of_injOn (center_injective_on R S (fun X hX ↦ (hshift X hX).1))] using hcount

end PaperP1.BoundedWidthDenseCount
