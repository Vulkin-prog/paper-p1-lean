module

public import PaperP1.Arithmetic.OriginalIntegerSourceCover
public import PaperP1.Arithmetic.OrdinaryCoverAtSystemFromExactSource
public import PaperP1.Arithmetic.UniformOrdinarySurfaceCoverFromExactSource

/-! # Unconditional ordinary integer-source covers with the original exact degree and height exponents -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerOrdinarySourceCover
open PaperP1 HomogeneousSplitRadicalData WeightedOrdinaryAffineIdeal
local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
theorem at_system (k E : ℕ) (hE : 0 < E) (B : ℕ) (A δ : ℝ)
    (hcover : IntegerExactSourceSurfaceCover.CoverAtSize k E hE B A δ)
    (s : List (PolynomialRing ℚ)) (hlen : s.length = k) (dZ : Fin k → ℤ) (I J : Fin k → Finset ℤ)
    (hs : ∀ i : Fin s.length, s.get i = radicand (dZ (Fin.cast hlen i) : ℚ)
      (2 * E - ((I (Fin.cast hlen i)).card + (J (Fin.cast hlen i)).card)) (I (Fin.cast hlen i)) (J (Fin.cast hlen i)))
    (hmin : ∀ i, 2 ≤ (I i).card + (J i).card) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * E)
    (hd : ∀ i, dZ i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
    (D : ℕ) (hD : 0 < D) (H : ℕ) (hH : 1 ≤ H) (U : Finset (OrdinaryIntegerPoints.Point (Fin k)))
    (hU : U ⊆ OrdinaryIntegerPoints.curvePoints (ordinaryIdeal (fun i ↦ (dZ i : ℚ)) I J) H) :
    ∃ (W : Finset (OrdinaryIntegerPoints.Point (Fin k))) (curves : Finset (OrdinarySurfaceCurveData.Curve (fun i ↦ (dZ i : ℚ)) D I J)),
      W ⊆ U ∧ (∀ Δ ∈ curves, Δ.degree ≤ B) ∧
      (W.card : ℝ) ≤ A * ((H ^ E : ℕ) : ℝ) ^ (2 / Real.sqrt ((2 ^ k * E ^ 2 : ℕ) : ℝ) + δ) ∧
      (curves.card : ℝ) ≤ A * ((H ^ E : ℕ) : ℝ) ^ (1 / Real.sqrt ((2 ^ k * E ^ 2 : ℕ) : ℝ) + δ) ∧
      ∀ v ∈ U, v ∉ W → ∃ Δ ∈ curves, v ∈ OrdinaryIntegerPoints.curvePoints Δ.ideal H := by
  classical
  let c : Fin k → ℚ := fun i ↦ (dZ i : ℚ)
  subst k
  let U' := U.image (OrdinarySourceIntegerLift.point E)
  have hU' : U' ⊆ SourceIntegerPoints.curvePoints E
      (RingHom.ker (SourceProjectiveEmbedding.evaluation c E I J hdeg hE).toRingHom) (H ^ E) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact OrdinarySourcePointTransport.point_mem_global c E I J hdeg hE H v (hU hv) hH
  have hHE : 1 ≤ H ^ E := one_le_pow₀ hH
  obtain ⟨V, family, _hV, hdegrees, hVbound, hcount, hpoints⟩ :=
    hcover s rfl dZ I J hs hdeg hd hne hI hJ (H ^ E) hHE U' hU'
  have hpoints' : ∀ v ∈ U, OrdinarySourceIntegerLift.point E v ∉ V → ∃ Γ ∈ family,
      OrdinarySourceIntegerLift.point E v ∈ SourceIntegerPoints.curvePoints E
        (SourceProjectiveCurveData.ideal s c E I J hdeg hE Γ) (H ^ E) := by
    intro v hv hnot
    exact hpoints _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩) hnot
  obtain ⟨W, curves, hW, hWcard, hcard, hdegrees', hresult⟩ :=
    OrdinarySourceFiniteCoverTransfer.exists_cover s c E I J hs hmin hdeg hE D hD H (H ^ E)
      U hU V family B hdegrees hpoints'
  refine ⟨W, curves, hW, hdegrees', ?_, ?_, hresult⟩
  · exact (show (W.card : ℝ) ≤ (V.card : ℝ) by exact_mod_cast hWcard).trans hVbound
  · exact (show (curves.card : ℝ) ≤ (family.card : ℝ) by exact_mod_cast hcard).trans hcount

theorem uniform_cover (kmax K : ℕ) : UniformOrdinarySurfaceCover.UniformCover kmax K := by
  let E := K + 1
  have hE : 0 < E := by dsimp only [E]; omega
  have hK : K ≤ 2 * E := by dsimp only [E]; omega
  have h := OriginalIntegerSourceCover.uniform_cover kmax E
  intro δ hδ
  obtain ⟨B, A, hA, hsource⟩ := h (δ / (E : ℝ)) (div_pos hδ (Nat.cast_pos.mpr hE))
  refine ⟨B, A, hA, ?_⟩
  intro k hk d I j hd hI hj hne hsize
  dsimp only
  intro D hD H hH U hU
  let s := OrdinaryRootSystemData.radicands k E d I j
  have hlen : s.length = k := OrdinaryRootSystemData.length k E d I j
  let c : Fin k → ℚ := fun i ↦ (d i : ℚ)
  let J₀ : Fin k → Finset ℤ := fun i ↦ {j i}
  have hs : ∀ i : Fin s.length, s.get i = radicand (c (Fin.cast hlen i))
      (2 * E - ((I (Fin.cast hlen i)).card + (J₀ (Fin.cast hlen i)).card))
      (I (Fin.cast hlen i)) (J₀ (Fin.cast hlen i)) := OrdinaryRootSystemData.get k E d I j
  have hmin (i : Fin k) : 2 ≤ (I i).card + (J₀ i).card := by
    have hi := (hne i).card_pos
    simp only [J₀, Finset.card_singleton]
    omega
  have hdeg (i : Fin k) : (I i).card + (J₀ i).card ≤ 2 * E := by
    simpa only [J₀, Finset.card_singleton] using (hsize i).trans hK
  have hJ : Pairwise fun i t ↦ Disjoint (J₀ i) (J₀ t) := by
    intro i t hne
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact hne (hj ((Finset.mem_singleton.mp hz).symm.trans (Finset.mem_singleton.mp hz')))
  obtain ⟨V, curves, _hV, hdegree, hVbound, hcount, hpoint⟩ :=
    at_system k E hE B A (δ / (E : ℝ)) (hsource hE k hk)
      s hlen d I J₀ hs hmin hdeg hd (fun i ↦ Or.inl (hne i)) hI hJ D hD H hH U hU
  refine ⟨V, curves, hdegree, ?_, ?_, hpoint⟩
  · simpa only [SourceOrdinaryCoverPower.height_power k E H hE 2 δ] using hVbound
  · simpa only [SourceOrdinaryCoverPower.height_power k E H hE 1 δ] using hcount

end IntegerOrdinarySourceCover
