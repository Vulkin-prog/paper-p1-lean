module

public import PaperP1.Analysis.TransposedGraphOverlapUniqueness
public import PaperP1.Analysis.NormalizedGraphImageNeighborhood

/-! # Genuine local coverage and relative openness in the second-coordinate orientation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TransposedGraphImageNeighborhood

open MvPolynomial Set PlaneCoordinateSwap TransposedGraphOverlapUniqueness


theorem continuous_point : Continuous (point : (Fin 2 → ℝ) → Fin 2 → ℝ) :=
  continuous_pi (fun i ↦ continuous_apply (index i))

theorem exists_open_neighborhood (P : MvPolynomial (Fin 2) ℝ) (q : TransposedNormalizedGraphPiece.Piece P)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo q.left q.right) :
    ∃ V : Set (Fin 2 → ℝ), IsOpen V ∧ (fun i ↦ q.path i t₀) ∈ V ∧
      ∀ w ∈ V, eval w P = 0 → w 1 ∈ Ioo q.left q.right ∧ (fun i ↦ q.path i (w 1)) = w := by
  obtain ⟨U, hopen, hmem, hcover⟩ :=
    NormalizedGraphImageNeighborhood.exists_open_neighborhood (polynomial P) (firstPiece P q) t₀ ht₀
  let V := point ⁻¹' U
  refine ⟨V, hopen.preimage continuous_point, hmem, ?_⟩
  intro w hw hzero
  have hswap : eval (point w) (polynomial P) = 0 := by
    rw [evaluation_polynomial_at_point]
    exact hzero
  obtain ⟨hparam, he⟩ := hcover (point w) hw hswap
  have hparam' : w 1 ∈ Ioo q.left q.right := by
    change point w 0 ∈ Ioo q.left q.right at hparam
    simpa only [point, index_zero] using hparam
  refine ⟨hparam', ?_⟩
  funext i
  have hi := congrFun he (index i)
  change q.path (index (index i)) (point w 0) = point w (index i) at hi
  simpa only [point, index_zero, index_twice] using hi

theorem image_relatively_open (P : MvPolynomial (Fin 2) ℝ) (q : TransposedNormalizedGraphPiece.Piece P) :
    ∃ V : Set (Fin 2 → ℝ), IsOpen V ∧
      (fun t ↦ fun i ↦ q.path i t) '' Ioo q.left q.right = {w | eval w P = 0} ∩ V := by
  classical
  choose U hUopen hUmem hUcover using fun t : Ioo q.left q.right ↦ exists_open_neighborhood P q t.val t.property
  let V := ⋃ t : Ioo q.left q.right, U t
  refine ⟨V, isOpen_iUnion hUopen, ?_⟩
  ext w
  constructor
  · intro hw
    obtain ⟨t, ht, rfl⟩ := hw
    exact ⟨q.equation t ht, mem_iUnion.mpr ⟨⟨t, ht⟩, hUmem ⟨t, ht⟩⟩⟩
  · rintro ⟨hzero, hw⟩
    obtain ⟨t, ht⟩ := mem_iUnion.mp hw
    obtain ⟨hx, he⟩ := hUcover t w ht hzero
    exact ⟨w 1, hx, he⟩

end PaperP1.TransposedGraphImageNeighborhood
