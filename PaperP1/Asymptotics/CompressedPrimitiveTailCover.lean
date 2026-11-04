module

public import PaperP1.Model.ChannelCompressedPrimitiveSets
public import PaperP1.Asymptotics.CompressedBlockIndependentTail

/-! # An exact finite cover of compressed primitive tails by actual independent block tails -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedPrimitiveTailCover

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.DyadicEndpointPairs PaperP1.CompressedSourceBlocks
  PaperP1.ChannelCompressedPrimitiveSets PaperP1.CompressedBlockIndependentTail

def centre (b L : ℕ) (i : Fin (L + 1)) (xy : ℕ × ℕ) : ℕ :=
  anchor b L i xy - b * (L + 1) + 1

theorem centre_injective {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 2 ≤ b)
    (hLN : L ≤ N) (hwidth : b * (L + 1) < N) (i j : Fin (L + 1)) :
    Set.InjOn (centre b L i) (sourcePairs N a b L i j) := by
  have hrecover (xy : ℕ × ℕ) (hxy : xy ∈ sourcePairs N a b L i j) :
      centre b L i xy + b * (L + 1) - 1 = anchor b L i xy := by
    have hh := CompressedAsymmetricCoarseProfile.anchor_mem_expanded hN hLN hb i j hxy
    have hlo := (mem_Ico.mp hh).1
    dsimp [centre]
    omega
  intro xy hxy uv huv heq
  apply first_anchor_injective (by omega) ha (by omega) i j hxy huv
  change anchor b L i xy = anchor b L i uv
  rw [← hrecover xy hxy, ← hrecover uv huv, heq]

theorem fixed_mass_bound {N a b L s : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (ha : 0 < a) (hb : 2 ≤ b) (hLN : L ≤ N)
    (hwidth : b * (L + 1) < N) (w R : ℝ) (hw : 0 < w) (hR : 0 ≤ R)
    (i j : Fin (L + 1))
    (hcap : ∀ xy ∈ sourcePairs N a b L i j, HomogeneousRunMass.probability L {xy.1, xy.2} ≤ R) :
    fixedMass N a b L s w i j ≤ (w * R * (2 ^ L : ℝ) ^ 2) *
      BoundedBlockIndependentTail.mass (3 * b + 2) N L s w (shiftedBlock N a b L i j) := by
  classical
  let K := w * R * (2 ^ L : ℝ) ^ 2
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hw.le hR) (sq_nonneg _)
  let f := fun x : ℕ ↦ (w * (2 ^ L : ℝ)⁻¹) *
    ∑ A ∈ OneBlockFullSupport.families (dyadicBlock N) L (shiftedBlock N a b L i j x) s,
      ∏ y ∈ A, w * infiniteMarginal y L
  have hf : ∀ x, 0 ≤ f x := fun x ↦ mul_nonneg (by positivity)
    (sum_nonneg fun A _ ↦ prod_nonneg fun y _ ↦
      mul_nonneg hw.le (MissingBlockProbabilities.infiniteMarginal_nonneg y L))
  have hrow (xy : ℕ × ℕ) (hxy : xy ∈ sourcePairs N a b L i j) :
      (∑ A ∈ targets N L s xy, weight L w xy A) ≤ K * f (centre b L i xy) := by
    have hblock := anchor_centre hN hLN hb hwidth i j hxy
    have hsub : targets N L s xy ⊆
        OneBlockFullSupport.families (dyadicBlock N) L
          (shiftedBlock N a b L i j (centre b L i xy)) s := by
      intro A hA
      obtain ⟨hAG, hsize, hp⟩ := mem_targets.mp hA
      have hspace : FiniteEvenSquareClasses.space
          (shiftedBlock N a b L i j (centre b L i xy)) = FixedPairExtensions.sourceSpace {xy.1, xy.2} L := by
        dsimp only [centre]
        rw [hblock.2, CompressedSourceBlocks.space_eq hN ha (by omega) i j hxy]
        exact (PaperP1.RetainedNullity.span_pair (fun x ↦ squareClassSpace x L) xy.1 xy.2).symm
      exact OneBlockFullSupport.mem_families _ _ _ _ _ |>.mpr
        ⟨hAG.trans (RegularStarts.regularStarts_subset N L), hsize,
          CompressedPrimitiveHomogeneousBounds.full_support L _ _ _ hspace hp⟩
    calc
      _ ≤ ∑ A ∈ targets N L s xy, K *
          ((w * (2 ^ L : ℝ)⁻¹) * ∏ y ∈ A, w * infiniteMarginal y L) := by
        apply sum_le_sum
        intro A hA
        obtain ⟨hAG, _hsize, hp⟩ := mem_targets.mp hA
        exact CompressedPrimitiveHomogeneousBounds.point_upper (by omega) hL xy A hAG hp
          w R hw.le (hcap xy hxy)
      _ = K * ((w * (2 ^ L : ℝ)⁻¹) *
          ∑ A ∈ targets N L s xy, ∏ y ∈ A, w * infiniteMarginal y L) := by
        rw [mul_sum, mul_sum]
      _ ≤ K * f (centre b L i xy) := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ ↦ prod_nonneg fun y _ ↦
          mul_nonneg hw.le (MissingBlockProbabilities.infiniteMarginal_nonneg y L))
  calc
    _ ≤ ∑ xy ∈ sourcePairs N a b L i j, K * f (centre b L i xy) := sum_le_sum hrow
    _ = K * ∑ xy ∈ sourcePairs N a b L i j, f (centre b L i xy) := (mul_sum _ _ _).symm
    _ ≤ K * ∑ x ∈ Ico 2 ((3 * b + 2) * N + 2), f x := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply sum_le_sum_of_injOn (centre b L i) (centre_injective hN ha hb hLN hwidth i j)
      · intro x hx
        obtain ⟨xy, hxy, rfl⟩ := mem_image.mp hx
        exact (anchor_centre hN hLN hb hwidth i j hxy).1
      · intro _ _
        exact le_rfl
      · intro x _ _
        exact hf x
    _ = _ := rfl

end PaperP1.CompressedPrimitiveTailCover
