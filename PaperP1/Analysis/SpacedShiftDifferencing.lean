module

public import PaperP1.Analysis.ShiftedCorrelations
public import PaperP1.Analysis.FiniteShiftDifferencing

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SpacedShiftDifferencing
open Finset PaperP1
open scoped Classical

def shifts (A K : ℕ) : Finset ℕ := (range K).image (fun j ↦ A*j)

theorem shifts_card (A K : ℕ) (hA : 0 < A) : (shifts A K).card=K := by
  have hi : Function.Injective (fun j : ℕ ↦ A*j) :=
    (show StrictMono (fun j : ℕ ↦ A*j) from fun _j _k hjk ↦ Nat.mul_lt_mul_of_pos_left hjk hA).injective
  rw [shifts,card_image_of_injective _ hi,card_range]

theorem shifts_upper (A K : ℕ) (hA : 0 < A) (h : ℕ) (hh : h ∈ shifts A K) : h < A*K := by
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hh
  exact Nat.mul_lt_mul_of_pos_left (mem_range.mp hj) hA

theorem distance_lower (A K : ℕ) (h k : ℕ) (hh : h ∈ shifts A K) (hk : k ∈ shifts A K)
    (hne : h ≠ k) : A ≤ Nat.dist h k := by
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hh
  obtain ⟨l,hl,rfl⟩ := mem_image.mp hk
  rcases le_total j l with hle | hle
  · have hstep : j+1 ≤ l := by
      have hne' : j ≠ l := by intro he; subst l; exact hne rfl
      omega
    have hm := Nat.mul_le_mul_left A hstep
    rw [Nat.dist_eq_sub_of_le (Nat.mul_le_mul_left A hle)]
    simp only [Nat.mul_add,Nat.mul_one] at hm
    omega
  · have hstep : l+1 ≤ j := by
      have hne' : j ≠ l := by intro he; subst l; exact hne rfl
      omega
    have hm := Nat.mul_le_mul_left A hstep
    rw [Nat.dist_eq_sub_of_le_right (Nat.mul_le_mul_left A hle)]
    simp only [Nat.mul_add,Nat.mul_one] at hm
    omega

theorem differencing_bound (N A K : ℕ) (hA : 0 < A) (hK : 0 < K)
    (a : ℕ → ℂ) (ha : ∀ n ∈ range N, ‖a n‖ ≤ 1) (E : ℝ) (hE : 0 ≤ E)
    (hCorr : ∀ d : ℕ, A ≤ d → d < A*K → ‖ShiftedCorrelations.correlation N a d‖ ≤ E) :
    ‖∑ n ∈ range N, a n‖^2 ≤ ((N+A*K : ℕ) : ℝ)*((N : ℝ)/(K : ℝ)+E) := by
  have hCard : 0 < (shifts A K).card := by rw [shifts_card A K hA]; exact hK
  have hh := FiniteShiftDifferencing.unit_off_diagonal_bound N (A*K) (shifts A K)
    (shifts_upper A K hA) hCard a ha E hE (by
      intro h hh k hk hne
      apply hCorr (Nat.dist h k) (distance_lower A K h k hh hk hne)
      have h1 := shifts_upper A K hA h hh
      have h2 := shifts_upper A K hA k hk
      rcases le_total h k with hle | hle
      · rw [Nat.dist_eq_sub_of_le hle]
        omega
      · rw [Nat.dist_eq_sub_of_le_right hle]
        omega)
  simpa only [shifts_card A K hA] using hh

theorem short_span_bound (N A K : ℕ) (hA : 0 < A) (hK : 0 < K) (hSpan : A*K ≤ N)
    (a : ℕ → ℂ) (ha : ∀ n ∈ range N, ‖a n‖ ≤ 1) (E : ℝ) (hE : 0 ≤ E)
    (hCorr : ∀ d : ℕ, A ≤ d → d < A*K → ‖ShiftedCorrelations.correlation N a d‖ ≤ E) :
    ‖∑ n ∈ range N, a n‖^2 ≤ 2*(N : ℝ)*((N : ℝ)/(K : ℝ)+E) := by
  have hh := differencing_bound N A K hA hK a ha E hE hCorr
  have hSize : ((N+A*K : ℕ) : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast (show N+A*K ≤ 2*N by omega)
  exact hh.trans (mul_le_mul_of_nonneg_right hSize (add_nonneg (by positivity) hE))
end PaperP1.SpacedShiftDifferencing
