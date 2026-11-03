module

public import PaperP1.Asymptotics.CriticalNonalignedPointCover
public import PaperP1.Asymptotics.SurfaceCurveCoverPowerBound
public import PaperP1.Arithmetic.UniformOrdinarySurfaceCover

/-! # Nonaligned integral point counts under two explicit uniform geometric inputs

Both the lifted Salberger covering and the uniform Pila curve count are
unproved explicit arguments. The actual degree exclusion, prime/field/chart
bridges, finite covering count and exponent choices are proved internally.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedSurfaceSubpowerUnderInputs

open Finset PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.WeightedOrdinaryAffineIdeal PaperP1.OrdinaryIntegerPoints PaperP1.CriticalNonalignedPointCover

theorem uniform_subpower (C q B₀ ε : ℝ) (K J : ℕ) (hq : 0 ≤ q) (hB₀ : 1 ≤ B₀) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ kmax ≥ k,
      UniformOrdinarySurfaceCover.UniformCover kmax K →
      (∀ M, UniformAffineCurvePointCount.UniformBound kmax M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ s : List (PolynomialRing ℚ), k ≤ s.length → s.length ≤ kmax →
      ∀ (d : Fin s.length → ℤ) (D : ℕ) (I : Fin s.length → Finset ℤ) (j : Fin s.length → ℤ),
      let c : Fin s.length → ℚ := fun i ↦ (d i : ℚ)
      let J₀ : Fin s.length → Finset ℤ := fun i ↦ {j i}
      ∀ (_hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J₀ i).card)) (I i) (J₀ i))
        (_hdeg : ∀ i, (I i).card + (J₀ i).card ≤ 2 * D) (_hD : 0 < D)
        (_hmin : ∀ i, 2 ≤ (I i).card + (J₀ i).card),
      ∀ a : ℕ, 0 < a → (∀ i, d i ≠ 0) →
        (Pairwise fun i t ↦ Disjoint (I i) (I t)) → Function.Injective j →
        (∀ i, (I i).card = a) → (∀ i, (I i).card + 1 ≤ K) →
        (∀ i, ∀ z ∈ I i, z.natAbs ≤ B) → (∀ i, (j i).natAbs ≤ B) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, j i ∈ T) →
      ∀ (U : Finset (Point (Fin s.length))) (H : ℕ), 1 ≤ H →
        (H : ℝ) ≤ B₀ * (N : ℝ) ^ q → U ⊆ curvePoints (ordinaryIdeal c I J₀) H →
        (∀ v ∈ U, Admissible N B S T v) → (U.card : ℝ) ≤ A * (N : ℝ) ^ ε ∧
          ((U.image host).card : ℝ) ≤ A * (N : ℝ) ^ ε := by
  obtain ⟨E, k, δ, _, hk, hδ, hfirst, hsecond⟩ := SurfaceCountParameters.subpower_parameters q ε hq hε
  refine ⟨k, ?_⟩
  intro kmax _hkkmax hCover hPila
  obtain ⟨M, C₀, hC₀, hcover⟩ := hCover δ hδ
  obtain ⟨A₁, hA₁, Ncut, hcount⟩ := eventually_finite_cover_bound C E J kmax M δ hδ (hPila M)
  let α := 2 / Real.sqrt ((2 : ℝ) ^ k) + δ
  let β := 1 / Real.sqrt ((2 : ℝ) ^ k) + δ
  let γ := 1 / ((E : ℝ) + 1) + δ
  let A := C₀ * B₀ ^ α + C₀ * A₁ * B₀ ^ (β + γ)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, max 1 Ncut, ?_⟩
  intro N hN L B hcrit hB hBL s hlength hcap d D I j c J₀ hs hdeg hD hmin a ha hd hI hj hcard hK hiB hjB S T hiS hjT U H hH hheight hU hadmiss
  have hne (i : Fin s.length) : (I i).Nonempty := card_pos.mp (by rw [hcard i]; omega)
  obtain ⟨V, curves, hM, hV, hcurves, hcovered⟩ :=
    hcover s.length hcap d I j hd hI hj hne hK D hD H hH U hU
  have hfinite := hcount N ((le_max_right 1 Ncut).trans hN) L B hcrit hB hBL s hcap d D I j hs hdeg hD hmin
    (hk.trans hlength) a ha hd hI hj hcard hiB hjB S T hiS hjT U V curves H hH hM hadmiss hcovered
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hdecay := UniformOrdinarySurfaceCover.decay_mono hlength
  have htwo : 2 / Real.sqrt ((2 : ℝ) ^ s.length) ≤ 2 / Real.sqrt ((2 : ℝ) ^ k) := by
    convert mul_le_mul_of_nonneg_left hdecay (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβγ : 0 ≤ β + γ := by dsimp [β, γ]; positivity
  have hV' : (V.card : ℝ) ≤ C₀ * (H : ℝ) ^ α := hV.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hHreal
      (add_le_add htwo (le_refl δ))) hC₀.le)
  have hcurves' : (curves.card : ℝ) ≤ C₀ * (H : ℝ) ^ β := hcurves.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hHreal
      (add_le_add hdecay (le_refl δ))) hC₀.le)
  have hαq : q * α ≤ ε := by
    calc
      q * α = 2 * q / Real.sqrt ((2 : ℝ) ^ k) + q * δ := by dsimp [α]; ring
      _ ≤ ε / 2 := hfirst
      _ ≤ ε := by linarith
  have hβγq : q * (β + γ) ≤ ε := by
    calc
      q * (β + γ) = q / Real.sqrt ((2 : ℝ) ^ k) + q / ((E : ℝ) + 1) + 2 * q * δ := by
        dsimp [β, γ]
        ring
      _ ≤ ε / 2 := hsecond
      _ ≤ ε := by linarith
  have hfinal := SurfaceCurveCoverPowerBound.finite_cover_bound N H B₀ q ε α β γ C₀ A₁
    (U.card : ℝ) (V.card : ℝ) (curves.card : ℝ) ((le_max_left 1 Ncut).trans hN) hH
    (by linarith) hα hβγ hC₀.le hA₁.le hheight hαq hβγq hfinite hV' hcurves'
  refine ⟨hfinal, ?_⟩
  have himage : ((U.image host).card : ℝ) ≤ (U.card : ℝ) := by exact_mod_cast (card_image_le : (U.image host).card ≤ U.card)
  exact himage.trans hfinal

end PaperP1.NonalignedSurfaceSubpowerUnderInputs
