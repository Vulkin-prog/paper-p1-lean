module

public import PaperP1.Asymptotics.ActualSourceClusterCount
public import PaperP1.Asymptotics.SourceCurveCover

/-! # The two full determinant bounds for the actual primitive signed source population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveSourceDeterminantCount

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantRelativeIntervals PaperP1.DeterminantIntervalPartition
open PaperP1.DeterminantHorizontalScale PaperP1.DeterminantLogScale PaperP1.DeterminantPositiveOrientation
open PaperP1.ActualProjectivePairs PaperP1.ConstructedClusterCurveData PaperP1.OccupiedDeterminantIntervals
open PaperP1.IntegerPairFactorCover PaperP1.QuadraticIntervalGrid PaperP1.IntegralSourceCoefficients

theorem uniform_primitive_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (δ C ρ Kbar Abar Kshift Aexp ε : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hKbar : 0 ≤ Kbar) (hAbar : 0 ≤ Abar) (hKshift : 0 ≤ Kshift) (hAexp : 0 ≤ Aexp) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ Kshift * (Real.log N) ^ Aexp →
      ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      ∀ Γ : ℝ, 0 ≤ Γ → Γ ≤ Kbar * (Real.log N) ^ Abar →
      (N : ℝ) ≤ Γ * X.c₁ * X.c₂ * (X.D * X.E) ^ 2 →
      ∀ S : Finset Quad, SignedPopulation X h S → (∀ p ∈ S, Primitive p) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε *
          min (Real.sqrt (X.D * X.E * Real.exp (logShape N X.D X.E X.U X.V)) + X.D + X.E)
            (Real.sqrt (X.U * X.V * Real.exp (logShape N X.D X.E X.U X.V)) + X.U + X.V) := by
  let η := ε / 8
  let ζ := min (ε / 8) (1 / 16)
  have hη : 0 < η := by dsimp [η]; positivity
  have hζ : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζsmall : ζ < 7 / 16 := (min_le_right _ _).trans_lt (by norm_num)
  have hgap : η + ζ / 2 < ε / 2 := by
    have hz : ζ ≤ ε / 8 := min_le_left _ _
    dsimp [η]
    linarith
  obtain ⟨B, Amax, κ₀, κ₁, κf, Ns, _hB, hs⟩ := SourceCurveCover.uniform_global_cover
    (ε / 2) η δ C ρ Kshift Aexp ζ hη hδ hC hρ hρ₁ hζ hζsmall hgap
  obtain ⟨Nc, hc⟩ := ActualSourceClusterCount.uniform_factor_sum_count hHB hNG Amax B κf
    C ρ Kbar Abar Kshift Aexp (ε / 2) hC hρ hKbar hAbar hKshift hAexp (by positivity)
  refine ⟨max 1 (max Ns Nc), ?_⟩
  intro N hN h hh hshift X coefs Γ hΓ hΓbound hbarrier S hS hprim
  let X' := orientedBox h X
  let M := horizontalScale N X.D X.E X.U X.V ζ
  let Z := Real.exp (logShape N X.D X.E X.U X.V)
  let S' := orientedPopulation h S
  let I := occupied M X'.D X'.E S'
  let coefs' : IntegerCoefficients X' := IntegralSourceCoefficients.oriented h coefs
  obtain ⟨hM, _hMN, hMh, A₀, B₀, A₁, B₁, L₀, L₁, T₀, T₁, hDdata, hUdata, hcurves⟩ :=
    hs N (by omega) h hh hshift X
  obtain ⟨F, hrange, hlocal, htotal, hLs, hTs⟩ := hcurves S hS hprim
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg hn.le _
  have hS' : SignedPopulation X' (h.natAbs : ℤ) S' :=
    DeterminantPositiveOrientation.signed_population X h S hS
  have hprim' : ∀ p ∈ S', Primitive p := oriented_primitive h S hprim
  have hh' : (h.natAbs : ℤ) ≠ 0 := by exact_mod_cast (Int.natAbs_pos.mpr hh).ne'
  have habs : |((h.natAbs : ℤ) : ℝ)| = |(h : ℝ)| := by
    have hz : |(h.natAbs : ℤ)| = |h| := by rw [Int.natCast_natAbs, abs_abs]
    exact_mod_cast hz
  have hshift' : |((h.natAbs : ℤ) : ℝ)| ≤ Kshift * (Real.log N) ^ Aexp := by simpa only [habs] using hshift
  have hnorm : (M : ℝ) * |((h.natAbs : ℤ) : ℝ)| ≤ N := by
    simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg h.natAbs : (0 : ℝ) ≤ h.natAbs)] using hMh
  have hproduct := barrier_orientation h X
  change X'.c₁ * X'.c₂ * (X'.D * X'.E) ^ 2 = X.c₁ * X.c₂ * (X.D * X.E) ^ 2 at hproduct
  have hbarrier' : (N : ℝ) ≤ Γ * X'.c₁ * X'.c₂ * (X'.D * X'.E) ^ 2 := by
    have ht : (N : ℝ) ≤ Γ * (X.c₁ * X.c₂ * (X.D * X.E) ^ 2) := by simpa only [mul_assoc] using hbarrier
    rw [← hproduct] at ht
    simpa only [mul_assoc] using ht
  let P := fun (k : ℕ) (c : Bool × Bool) ↦ FourProjectiveCharts.population c
    ((cluster M X'.D X'.E k S').image (coordinates (B₀ k) (B₁ (grid M k))))
  let mass := fun k : ℕ ↦ (((∑ c : Bool × Bool, ∑ G ∈ F k c, (zeros G (P k c)).card) : ℕ) : ℝ)
  have htotalR : (S.card : ℝ) ≤ ∑ k ∈ I, mass k := by
    dsimp only [mass, P]
    exact_mod_cast htotal
  have hcount (k : ℕ) (hk : k ∈ I) : mass k ≤ (N : ℝ) ^ (ε / 2) * min (L₀ k) (T₀ (grid M k)) := by
    have hD := hDdata k (hrange k hk).2
    have hU := hUdata (grid M k) (grid_upper M k (by omega) (hrange k hk).2)
    exact hc N (by omega) δ X' coefs' Γ hΓ hΓbound hbarrier' κ₀ κ₁ M k
      (A₀ k) (B₀ k) (A₁ (grid M k)) (B₁ (grid M k)) (L₀ k) (L₁ k) (T₀ (grid M k)) (T₁ (grid M k))
      hD hU (by omega) (h.natAbs : ℤ) hh' hshift' hnorm S' hS' hprim' (F k) (hlocal k hk)
  have hmassL : (S.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) * (∑ k ∈ I, L₀ k) := by
    apply htotalR.trans
    calc
      _ ≤ ∑ k ∈ I, (N : ℝ) ^ (ε / 2) * L₀ k := sum_le_sum (fun k hk ↦
        (hcount k hk).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hpow))
      _ = _ := by rw [mul_sum]
  have hmassT : (S.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) * (∑ k ∈ I, T₀ (grid M k)) := by
    apply htotalR.trans
    calc
      _ ≤ ∑ k ∈ I, (N : ℝ) ^ (ε / 2) * T₀ (grid M k) := sum_le_sum (fun k hk ↦
        (hcount k hk).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hpow))
      _ = _ := by rw [mul_sum]
  have hleft : (S.card : ℝ) ≤ (N : ℝ) ^ ε * (Real.sqrt (X.D * X.E * Z) + X.D + X.E) := by
    calc
      _ ≤ (N : ℝ) ^ (ε / 2) * (∑ k ∈ I, L₀ k) := hmassL
      _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * (Real.sqrt (X.D * X.E * Z) + X.D + X.E)) :=
        mul_le_mul_of_nonneg_left hLs hpow
      _ = _ := by rw [← mul_assoc, ← Real.rpow_add hn]; congr 2; ring
  have hright : (S.card : ℝ) ≤ (N : ℝ) ^ ε * (Real.sqrt (X.U * X.V * Z) + X.U + X.V) := by
    calc
      _ ≤ (N : ℝ) ^ (ε / 2) * (∑ k ∈ I, T₀ (grid M k)) := hmassT
      _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * (Real.sqrt (X.U * X.V * Z) + X.U + X.V)) :=
        mul_le_mul_of_nonneg_left hTs hpow
      _ = _ := by rw [← mul_assoc, ← Real.rpow_add hn]; congr 2; ring
  change (S.card : ℝ) ≤ (N : ℝ) ^ ε * min (Real.sqrt (X.D * X.E * Z) + X.D + X.E)
    (Real.sqrt (X.U * X.V * Z) + X.U + X.V)
  rcases le_total (Real.sqrt (X.D * X.E * Z) + X.D + X.E) (Real.sqrt (X.U * X.V * Z) + X.U + X.V) with hcost | hcost
  · simpa only [min_eq_left hcost] using hleft
  · simpa only [min_eq_right hcost] using hright

theorem uniform_literal_primitive_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (δ C ρ Kshift Aexp ε : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hKshift : 0 ≤ Kshift) (hAexp : 0 ≤ Aexp) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ Kshift * (Real.log N) ^ Aexp →
      ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      (N : ℝ) ≤ X.c₁ * X.c₂ * (X.D * X.E) ^ 2 →
      ∀ S : Finset Quad, SignedPopulation X h S → (∀ p ∈ S, Primitive p) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε *
          min (Real.sqrt (X.D * X.E * Real.exp (logShape N X.D X.E X.U X.V)) + X.D + X.E)
            (Real.sqrt (X.U * X.V * Real.exp (logShape N X.D X.E X.U X.V)) + X.U + X.V) := by
  obtain ⟨N₀, hN₀⟩ := uniform_primitive_count hHB hNG δ C ρ 1 0 Kshift Aexp ε
    hδ hC hρ hρ₁ (by norm_num) (by norm_num) hKshift hAexp hε
  refine ⟨N₀, ?_⟩
  intro N hN h hh hshift X coefs hbarrier S hS hprim
  exact hN₀ N hN h hh hshift X coefs 1 (by norm_num) (by simp)
    (by simpa only [one_mul] using hbarrier) S hS hprim

end PaperP1.PrimitiveSourceDeterminantCount
