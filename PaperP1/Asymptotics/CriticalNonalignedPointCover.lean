module

public import PaperP1.Asymptotics.CriticalNonalignedDegreeGap
public import PaperP1.Arithmetic.UniformAffineCurvePointCount
public import PaperP1.Combinatorics.FiniteCoverCount

/-! # Counting nonaligned ordinary integral points without host independence

The only unproved point-count input is the explicit uniform affine-curve
property. The finite covering sets, their degree caps, and their cardinality
bounds are not produced by a surface-covering theorem in this module.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalNonalignedPointCover

open Finset PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.OrdinarySurfaceCurveData PaperP1.OrdinaryIntegerPoints PaperP1.SelectedProportionalPairs

def Admissible {ι : Type*} (N B : ℕ) (S T : Finset ℤ) (v : Point ι) : Prop :=
  (N : ℤ) ≤ v (Sum.inl 1) ∧ (N : ℤ) ≤ v (Sum.inl 0) ∧ (v (Sum.inl 0)).natAbs ≤ 2 * N ∧
    (∀ z ∈ S, 0 < v (Sum.inl 1) + z) ∧ (∀ z ∈ T, 0 < v (Sum.inl 0) + z) ∧
    ¬ AffineGridAlignment.Aligned B (v (Sum.inl 1)) (v (Sum.inl 0))

theorem eventually_finite_cover_bound (C : ℝ) (E J kmax M : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hPila : UniformAffineCurvePointCount.UniformBound kmax M) :
    ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ s : List (PolynomialRing ℚ), s.length ≤ kmax →
      ∀ (d : Fin s.length → ℤ) (D : ℕ) (I : Fin s.length → Finset ℤ) (j : Fin s.length → ℤ),
      let c : Fin s.length → ℚ := fun i ↦ (d i : ℚ)
      let J₀ : Fin s.length → Finset ℤ := fun i ↦ {j i}
      ∀ (_hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J₀ i).card)) (I i) (J₀ i))
        (_hdeg : ∀ i, (I i).card + (J₀ i).card ≤ 2 * D) (_hD : 0 < D)
        (_hmin : ∀ i, 2 ≤ (I i).card + (J₀ i).card),
        4 * (E + 1) ^ 2 ≤ s.length →
      ∀ a : ℕ, 0 < a → (∀ i, d i ≠ 0) →
        (Pairwise fun i k ↦ Disjoint (I i) (I k)) → Function.Injective j →
        (∀ i, (I i).card = a) → (∀ i, ∀ z ∈ I i, z.natAbs ≤ B) → (∀ i, (j i).natAbs ≤ B) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, j i ∈ T) →
      ∀ (U V : Finset (Point (Fin s.length))) (curves : Finset (Curve c D I J₀)) (H : ℕ),
        1 ≤ H → (∀ Γ ∈ curves, Γ.degree ≤ M) → (∀ v ∈ U, Admissible N B S T v) →
        (∀ v ∈ U, v ∉ V → ∃ Γ ∈ curves, v ∈ curvePoints Γ.ideal H) →
        (U.card : ℝ) ≤ (V.card : ℝ) + (curves.card : ℝ) * A * (H : ℝ) ^ (1 / ((E : ℝ) + 1) + δ) := by
  obtain ⟨A, hA, hpoint⟩ := UniformAffineCurvePointCount.high_degree_bound kmax M E hPila δ hδ
  obtain ⟨N₀, hN₀⟩ := CriticalNonalignedDegreeGap.eventually_degree_gt C E J
  refine ⟨A, hA, N₀, ?_⟩
  intro N hN L B hcrit hB hBL s hlength d D I j c J₀ hs hdeg hD hmin hlarge a ha hd hI hj hcard hiB hjB S T hiS hjT U V curves H hH hM hadmiss hcover
  classical
  let large := curves.filter (fun Γ ↦ E < Γ.degree)
  have hlarge_cover : ∀ v ∈ U \ V, ∃ Γ ∈ large, v ∈ curvePoints Γ.ideal H := by
    intro v hv
    obtain ⟨hvU, hvV⟩ := mem_sdiff.mp hv
    obtain ⟨Γ, hΓ, hvΓ⟩ := hcover v hvU hvV
    obtain ⟨⟨_, hZ⟩, hker⟩ := (mem_curvePoints Γ.ideal H v).mp hvΓ
    obtain ⟨hx, hylo, hy, hposS, hposT, hnonaligned⟩ := hadmiss v hvU
    let := Γ.prime
    have hρZ : evaluation v (MvPolynomial.X (Sum.inl (2 : Fin 3))) = 1 := by
      rw [evaluation_X, hZ]
      norm_num
    have hgap := hN₀ N hN L B hcrit hB hBL s d D I j hs hdeg hD hmin Γ.ideal Γ.relations
      Γ.homogeneous Γ.degree Γ.constant Γ.hilbert Γ.height hlarge a ha hd hI hj hcard hiB hjB S T hiS hjT
      (v (Sum.inl 1)) (v (Sum.inl 0)) hx hylo hy (evaluation v) (evaluation_X v _) (evaluation_X v _)
      hρZ hker hposS hposT hnonaligned
    exact ⟨Γ, mem_filter.mpr ⟨hΓ, hgap⟩, hvΓ⟩
  have hF : ∀ Γ ∈ large,
      ((curvePoints Γ.ideal H).card : ℝ) ≤ A * (H : ℝ) ^ (1 / ((E : ℝ) + 1) + δ) := by
    intro Γ hΓ
    obtain ⟨hΓmem, hgap⟩ := mem_filter.mp hΓ
    exact hpoint s.length hlength c D I J₀ Γ (hM Γ hΓmem) hgap H hH
  have hcount := FiniteCoverCount.cardinal_le (U \ V) large (fun Γ ↦ curvePoints Γ.ideal H)
    (A * (H : ℝ) ^ (1 / ((E : ℝ) + 1) + δ)) hlarge_cover hF
  have hnum : (large.card : ℝ) ≤ curves.card := by
    exact_mod_cast card_le_card (filter_subset _ _)
  have hcount' : ((U \ V).card : ℝ) ≤ (curves.card : ℝ) *
      (A * (H : ℝ) ^ (1 / ((E : ℝ) + 1) + δ)) :=
    hcount.trans (mul_le_mul_of_nonneg_right hnum (mul_nonneg hA.le (Real.rpow_nonneg (Nat.cast_nonneg H) _)))
  have hsub : U ⊆ V ∪ (U \ V) := by
    intro v hv
    by_cases hV : v ∈ V
    · exact mem_union_left _ hV
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hv, hV⟩)
  have hcardU : (U.card : ℝ) ≤ (V.card : ℝ) + ((U \ V).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le V (U \ V))
  exact hcardU.trans (by simpa only [mul_assoc] using add_le_add (le_refl (V.card : ℝ)) hcount')

end PaperP1.CriticalNonalignedPointCover
