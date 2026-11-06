module

public import PaperP1.Analysis.ReciprocalFrequencyWeights

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.TranslatedFrequencyTail
open Finset PaperP1
open scoped Classical

theorem left_bound (S : Finset ℕ) (K : ℕ) (R : ℝ) (hR : 0 < R)
    (hS : ∀ j ∈ S, j < K ∧ R ≤ (K : ℝ)-(j : ℝ)) :
    (∑ j ∈ S, 1/(1+((j : ℝ)-(K : ℝ))^2)) ≤ 2/R := by
  have hinj : Set.InjOn (fun j : ℕ ↦ K-j) S := by
    intro j hj k hk he
    have hjK := (hS j hj).1
    have hkK := (hS k hk).1
    change K-j=K-k at he
    omega
  have hh := ReciprocalSquareTail.finite_bound R hR (S.image (fun j ↦ K-j)) (by
    intro n hn
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hn
    rw [Nat.cast_sub (hS j hj).1.le]
    exact (hS j hj).2)
  rw [sum_image hinj] at hh
  apply le_trans _ hh
  apply sum_le_sum
  intro j hj
  rw [Nat.cast_sub (hS j hj).1.le]
  have hp : 0 < (K : ℝ)-(j : ℝ) := hR.trans_le (hS j hj).2
  apply one_div_le_one_div_of_le (sq_pos_of_pos hp)
  nlinarith

theorem right_bound (S : Finset ℕ) (K : ℕ) (R : ℝ) (hR : 0 < R)
    (hS : ∀ j ∈ S, K < j ∧ R ≤ (j : ℝ)-(K : ℝ)) :
    (∑ j ∈ S, 1/(1+((j : ℝ)-(K : ℝ))^2)) ≤ 2/R := by
  have hinj : Set.InjOn (fun j : ℕ ↦ j-K) S := by
    intro j hj k hk he
    have hKj := (hS j hj).1
    have hKk := (hS k hk).1
    change j-K=k-K at he
    omega
  have hh := ReciprocalSquareTail.finite_bound R hR (S.image (fun j ↦ j-K)) (by
    intro n hn
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hn
    rw [Nat.cast_sub (hS j hj).1.le]
    exact (hS j hj).2)
  rw [sum_image hinj] at hh
  apply le_trans _ hh
  apply sum_le_sum
  intro j hj
  rw [Nat.cast_sub (hS j hj).1.le]
  have hp : 0 < (j : ℝ)-(K : ℝ) := hR.trans_le (hS j hj).2
  exact one_div_le_one_div_of_le (sq_pos_of_pos hp) (by linarith)

theorem finite_bound (S : Finset ℕ) (K : ℕ) (R : ℝ) (hR : 0 < R)
    (hS : ∀ j ∈ S, R ≤ |(j : ℝ)-(K : ℝ)|) :
    (∑ j ∈ S, 1/(1+((j : ℝ)-(K : ℝ))^2)) ≤ 4/R := by
  let L := S.filter (fun j ↦ j<K)
  let U := S.filter (fun j ↦ K<j)
  have hLeft := left_bound L K R hR (by
    intro j hj
    obtain ⟨hjS,hjK⟩ := mem_filter.mp hj
    have hh := hS j hjS
    have hReal : (j : ℝ) ≤ K := by exact_mod_cast hjK.le
    rw [abs_of_nonpos (sub_nonpos.mpr hReal)] at hh
    exact ⟨hjK,by linarith only [hh]⟩)
  have hRight := right_bound U K R hR (by
    intro j hj
    obtain ⟨hjS,hKj⟩ := mem_filter.mp hj
    have hh := hS j hjS
    have hReal : (K : ℝ) ≤ j := by exact_mod_cast hKj.le
    rw [abs_of_nonneg (sub_nonneg.mpr hReal)] at hh
    exact ⟨hKj,hh⟩)
  have hSplit : (∑ j ∈ S, 1/(1+((j : ℝ)-(K : ℝ))^2)) ≤
      (∑ j ∈ L, 1/(1+((j : ℝ)-(K : ℝ))^2))+
      (∑ j ∈ U, 1/(1+((j : ℝ)-(K : ℝ))^2)) := by
    unfold L U
    rw [sum_filter,sum_filter,← sum_add_distrib]
    apply sum_le_sum
    intro j hj
    by_cases hL : j<K
    · simp [hL,show ¬K<j by omega]
    · by_cases hU : K<j
      · simp [hL,hU]
      · have he : j=K := by omega
        subst j
        have hh := hS K hj
        simp only [sub_self,abs_zero] at hh
        linarith only [hh,hR]
  exact hSplit.trans ((add_le_add hLeft hRight).trans_eq (by ring))
end PaperP1.TranslatedFrequencyTail
