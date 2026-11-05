module

public import PaperP1.Analysis.NormalizedGraphOverlapUniqueness

/-! # Genuine local coverage and relative openness of actual normalized graph images -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedGraphImageNeighborhood

open MvPolynomial Set Filter LocalNormalizedGraphPiece PolynomialVerticalRootUniqueness
open scoped Topology ContDiff


theorem exists_open_neighborhood (P : MvPolynomial (Fin 2) ℝ) (q : Piece P)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo q.left q.right) :
    ∃ U : Set (Fin 2 → ℝ), IsOpen U ∧ (fun i ↦ q.path i t₀) ∈ U ∧
      ∀ w ∈ U, eval w P = 0 → w 0 ∈ Ioo q.left q.right ∧ (fun i ↦ q.path i (w 0)) = w := by
  let z : Fin 2 → ℝ := fun i ↦ q.path i t₀
  obtain ⟨ρ, hρ, hroot⟩ := exists_local_vertical_unique P z (q.trajectory.1 t₀ ht₀)
  have hc : ContinuousAt (q.path 1) t₀ :=
    (GraphTangentSmooth.contDiffOn_trajectory P q.path (Ioo q.left q.right) isOpen_Ioo q.trajectory 1)
      |>.continuousOn.continuousAt (isOpen_Ioo.mem_nhds ht₀)
  have hcx : ContinuousAt (fun t : ℝ ↦ |t - t₀|) t₀ := (continuousAt_id.sub continuousAt_const).abs
  have hcy : ContinuousAt (fun t : ℝ ↦ |q.path 1 t - z 1|) t₀ := (hc.sub continuousAt_const).abs
  have hnearx : ∀ᶠ t in 𝓝 t₀, |t - t₀| < ρ :=
    hcx.eventually_lt continuousAt_const (by simpa only [sub_self, abs_zero] using hρ)
  have hneary : ∀ᶠ t in 𝓝 t₀, |q.path 1 t - z 1| < ρ :=
    hcy.eventually_lt continuousAt_const (by simpa only [z, sub_self, abs_zero] using hρ)
  have hn : {t : ℝ | t ∈ Ioo q.left q.right ∧ |t - t₀| < ρ ∧ |q.path 1 t - z 1| < ρ} ∈ 𝓝 t₀ :=
    Filter.inter_mem (isOpen_Ioo.mem_nhds ht₀) (Filter.inter_mem hnearx hneary)
  obtain ⟨a, b, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  let U : Set (Fin 2 → ℝ) := {w | w 0 ∈ Ioo a b ∧ |w 1 - z 1| < ρ}
  have hV : Continuous (fun w : Fin 2 → ℝ ↦ |w 1 - z 1|) := ((continuous_apply 1).sub continuous_const).abs
  have hopen : IsOpen U := (isOpen_Ioo.preimage (continuous_apply 0)).inter (isOpen_lt hV continuous_const)
  refine ⟨U, hopen, ?_, ?_⟩
  · constructor
    · change q.path 0 t₀ ∈ Ioo a b
      rw [q.first_coordinate t₀ ht₀]
      exact hmem
    · change |q.path 1 t₀ - q.path 1 t₀| < ρ
      simpa only [sub_self, abs_zero] using hρ
  · intro w hw hzero
    have hi := hsub hw.1
    have hx : |w 0 - z 0| < ρ := by
      change |w 0 - q.path 0 t₀| < ρ
      rw [q.first_coordinate t₀ ht₀]
      exact hi.2.1
    have hp : eval ![w 0, q.path 1 (w 0)] P = 0 := by
      have he : ![w 0, q.path 1 (w 0)] = (fun i ↦ q.path i (w 0)) := by
        funext i
        fin_cases i
        · exact (q.first_coordinate (w 0) hi.1).symm
        · rfl
      rw [he]
      exact q.equation (w 0) hi.1
    have hpw : eval ![w 0, w 1] P = 0 := by rw [point_eta]; exact hzero
    have hy := hroot (w 0) (q.path 1 (w 0)) (w 1) hx hi.2.2 hw.2 hp hpw
    refine ⟨hi.1, ?_⟩
    funext i
    fin_cases i
    · exact q.first_coordinate (w 0) hi.1
    · exact hy

theorem image_relatively_open (P : MvPolynomial (Fin 2) ℝ) (q : Piece P) :
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
    exact ⟨w 0, hx, he⟩

end PaperP1.NormalizedGraphImageNeighborhood
