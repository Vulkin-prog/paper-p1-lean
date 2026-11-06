module

public import Mathlib.Data.Nat.Dist
public import PaperP1.Analysis.ShiftedCorrelations

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.TriangularDifferencing
open Finset PaperP1
open scoped Classical

theorem reverse_sum (H : ℕ) (F : ℕ → ℝ) :
    (∑ k ∈ range H, F (H-k))=∑ d ∈ Icc 1 H, F d := by
  apply sum_bij (fun k _hk ↦ H-k)
  · intro k hk
    have hb := mem_range.mp hk
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro k hk j hj he
    have hk' := mem_range.mp hk
    have hj' := mem_range.mp hj
    omega
  · intro d hd
    have hd' := mem_Icc.mp hd
    refine ⟨H-d,mem_range.mpr (by omega),by omega⟩
  · intro k hk
    rfl

theorem distance_sum (H : ℕ) (F : ℕ → ℝ) :
    (∑ h ∈ range H, ∑ k ∈ range H, F (Nat.dist h k))=
      (H : ℝ)*F 0+2*(∑ h ∈ range H, ∑ d ∈ Icc 1 h, F d) := by
  induction H with
  | zero => simp
  | succ H ih =>
    have h1 : (∑ h ∈ range H, F (Nat.dist h H))=∑ d ∈ Icc 1 H, F d := by
      calc
        _ = ∑ h ∈ range H, F (H-h) := sum_congr rfl (fun h hh ↦ by
          rw [Nat.dist_eq_sub_of_le (mem_range.mp hh).le])
        _ = _ := reverse_sum H F
    have h2 : (∑ k ∈ range H, F (Nat.dist H k))=∑ d ∈ Icc 1 H, F d := by
      calc
        _ = ∑ k ∈ range H, F (H-k) := sum_congr rfl (fun k hk ↦ by
          rw [Nat.dist_eq_sub_of_le_right (mem_range.mp hk).le])
        _ = _ := reverse_sum H F
    have hrec : (∑ h ∈ range (H+1), ∑ k ∈ range (H+1), F (Nat.dist h k))=
        (∑ h ∈ range H, ∑ k ∈ range H, F (Nat.dist h k))+2*(∑ d ∈ Icc 1 H, F d)+F 0 := by
      simp only [sum_range_succ,sum_add_distrib]
      rw [h1,h2,Nat.dist_self]
      ring
    rw [hrec,ih,sum_range_succ]
    push_cast
    ring

theorem triangular_bound (N H : ℕ) (hH : 0 < H) (a : ℕ → ℂ) :
    ‖∑ n ∈ range N, a n‖^2 ≤
      (((N+H : ℕ) : ℝ)/(H : ℝ)^2)*((H : ℝ)*(∑ n ∈ range N, ‖a n‖^2)+
        2*(∑ h ∈ range H, ∑ d ∈ Icc 1 h, ‖ShiftedCorrelations.correlation N a d‖)) := by
  have hh := ShiftedCorrelations.differencing_bound N H hH a
  rw [distance_sum H (fun d ↦ ‖ShiftedCorrelations.correlation N a d‖),ShiftedCorrelations.zero_correlation_norm] at hh
  exact hh

theorem inverse_correlation_bound (N H : ℕ) (hH : 0 < H) (a : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ d ∈ Icc 1 H, ‖ShiftedCorrelations.correlation N a d‖ ≤ B/(d : ℝ)) :
    ‖∑ n ∈ range N, a n‖^2 ≤
      (((N+H : ℕ) : ℝ)/(H : ℝ))*((∑ n ∈ range N, ‖a n‖^2)+
        2*B*(∑ d ∈ Icc 1 H, 1/(d : ℝ))) := by
  have hs : (∑ h ∈ range H, ∑ d ∈ Icc 1 h, ‖ShiftedCorrelations.correlation N a d‖) ≤
      (H : ℝ)*B*(∑ d ∈ Icc 1 H, 1/(d : ℝ)) := by
    calc
      _ ≤ ∑ h ∈ range H, B*(∑ d ∈ Icc 1 H, 1/(d : ℝ)) := by
        apply sum_le_sum
        intro h hh
        have hsub : Icc 1 h ⊆ Icc 1 H := Icc_subset_Icc le_rfl (mem_range.mp hh).le
        calc
          _ ≤ ∑ d ∈ Icc 1 h, B/(d : ℝ) := sum_le_sum (fun d hd ↦ hc d (hsub hd))
          _ ≤ ∑ d ∈ Icc 1 H, B/(d : ℝ) := sum_le_sum_of_subset_of_nonneg hsub
            (fun d _hd _hnot ↦ div_nonneg hB (Nat.cast_nonneg d))
          _ = _ := by simp only [mul_sum]; apply sum_congr rfl; intro d hd; ring
      _ = _ := by simp only [sum_const,nsmul_eq_mul,card_range]; ring
  have hh := (triangular_bound N H hH a).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2)))
      (by positivity : 0 ≤ ((N+H : ℕ) : ℝ)/(H : ℝ)^2))
  convert hh using 1
  have hHr : (H : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hH)
  field_simp [hHr]
end PaperP1.TriangularDifferencing
