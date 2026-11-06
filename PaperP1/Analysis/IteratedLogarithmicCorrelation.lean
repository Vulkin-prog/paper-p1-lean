module

public import PaperP1.Analysis.ShiftedCorrelations
public import PaperP1.Analysis.IteratedLogarithmicPhase
public import PaperP1.Analysis.IteratedLogarithmicSum

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.IteratedLogarithmicCorrelation
open Finset PaperP1 IteratedLogarithmicPhase
open scoped Classical

def sequence (hs : List ℝ) (t : ℝ) (X n : ℕ) : ℂ := function hs t ((X+n : ℕ) : ℝ)

theorem sequence_norm (hs : List ℝ) (t : ℝ) (X n : ℕ) : ‖sequence hs t X n‖=1 := function_norm _ _ _

theorem sequence_sum_identity (hs : List ℝ) (t : ℝ) (X L : ℕ) :
    (∑ n ∈ range L, sequence hs t X n)=∑ n ∈ Ico X (X+L), function hs t n := by
  rw [sum_Ico_eq_sum_range,Nat.add_sub_cancel_left]
  rfl

theorem correlation_sequence_identity (hs : List ℝ) (t : ℝ) (X L d : ℕ) :
    ShiftedCorrelations.correlation L (sequence hs t X) d=
      ∑ n ∈ range (L-d), sequence ((d : ℝ)::hs) t X n := by
  rw [sequence_sum_identity]
  unfold ShiftedCorrelations.correlation
  rw [sum_Ico_eq_sum_range,Nat.add_sub_cancel_left]
  apply sum_congr rfl
  intro n hn
  dsimp only [sequence]
  rw [function_cons]
  simp only [Nat.cast_add,add_assoc]

theorem correlation_identity (hs : List ℝ) (t : ℝ) (X L d : ℕ) :
    ShiftedCorrelations.correlation L (sequence hs t X) d=
      ∑ n ∈ Ico X (X+(L-d)), function ((d : ℝ)::hs) t n := by
  rw [ShiftedCorrelations.correlation,sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  apply sum_congr rfl
  intro n hn
  dsimp only [sequence]
  rw [function_cons]
  simp only [Nat.cast_add,add_assoc]

theorem correlation_trivial_bound (hs : List ℝ) (t : ℝ) (X L d : ℕ) :
    ‖ShiftedCorrelations.correlation L (sequence hs t X) d‖ ≤ ((L-d : ℕ) : ℝ) := by
  unfold ShiftedCorrelations.correlation
  calc
    _ ≤ ∑ n ∈ range (L-d), ‖sequence hs t X n*star (sequence hs t X (n+d))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul,norm_star,sequence_norm,sum_const,nsmul_eq_mul,card_range,mul_one]

theorem correlation_bound (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (t : ℝ) (ht : t ≠ 0)
    (X L d : ℕ) (hX : 0 < X) (hd : 0 < d) (hdL : d ≤ L) :
    ‖ShiftedCorrelations.correlation L (sequence hs t X) d‖ ≤
      2*(((X+L : ℕ) : ℝ)+hs.sum)^(hs.length+2)/
        (|t| * ((hs.length+1).factorial : ℝ)*((d : ℝ)*hs.prod))+
      ((L-d : ℕ) : ℝ)*(|t| * (((hs.length+1).factorial : ℝ)*((d : ℝ)*hs.prod))/(X : ℝ)^(hs.length+2)) := by
  have hNew : ∀ h ∈ ((d : ℝ)::hs), 0 < h := by
    intro h hh
    rcases List.mem_cons.mp hh with he | he
    · rw [he]
      exact_mod_cast hd
    · exact hhs h he
  have hBound := IteratedLogarithmicSum.integer_sum_bound ((d : ℝ)::hs) hNew
    X (X+(L-d)) hX (by omega) t ht
  have hEndpoint : (((X+(L-d) : ℕ) : ℝ)+((d : ℝ)::hs).sum)=(((X+L : ℕ) : ℝ)+hs.sum) := by
    simp only [List.sum_cons,Nat.cast_add,Nat.cast_sub hdL]
    ring
  rw [hEndpoint] at hBound
  rw [correlation_identity]
  simpa only [List.length_cons,List.prod_cons,Nat.add_sub_cancel_left,Nat.add_assoc] using hBound
end PaperP1.IteratedLogarithmicCorrelation
