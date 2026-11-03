module

public import PaperP1.Arithmetic.ShortPrimePassage
public import PaperP1.Combinatorics.TopProductSelection

/-! # Deterministic finite product stopping and logarithmic factor confinement -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProductConfinement

open Finset

theorem card_le_log (P : Finset ℕ) (Y N : ℝ) (hY : 1 < Y)
    (hP : ∀ g ∈ P, Y < (g : ℝ)) (hprod : (P.prod id : ℕ) ≤ N) :
    P.card ≤ ⌊Real.log N / Real.log Y⌋₊ := by
  have hpos (g : ℕ) (hg : g ∈ P) : (0 : ℝ) < g := (by linarith : 0 < Y).trans (hP g hg)
  have hprodpos : (0 : ℝ) < (P.prod id : ℕ) := by
    rw [Nat.cast_prod]
    exact prod_pos hpos
  have hlog : (P.card : ℝ) * Real.log Y ≤ Real.log N := by
    calc
      _ = ∑ _g ∈ P, Real.log Y := by simp
      _ ≤ ∑ g ∈ P, Real.log g := sum_le_sum (fun g hg ↦
        Real.log_le_log (by linarith) (hP g hg).le)
      _ = Real.log (P.prod id : ℕ) := by
        simp only [Nat.cast_prod, id_eq]
        rw [Real.log_prod (fun g hg ↦ (hpos g hg).ne')]
      _ ≤ _ := Real.log_le_log hprodpos hprod
  exact Nat.le_floor ((le_div_iff₀ (Real.log_pos hY)).mpr hlog)

theorem stopping_subset (P : Finset ℕ) (N Z : ℝ) (hN : 1 ≤ N) (hZ : 0 ≤ Z)
    (hupper : ∀ g ∈ P, (g : ℝ) ≤ Z)
    (hlarge : N < (P.prod id : ℕ)) :
    ∃ A ⊆ P, N < (A.prod id : ℕ) ∧ (A.prod id : ℕ) ≤ N * Z := by
  classical
  let C := P.powerset.filter fun A ↦ N < (A.prod id : ℕ)
  have hPC : P ∈ C := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hlarge⟩
  obtain ⟨A, hAC, hmin⟩ := exists_min_image C Finset.card ⟨P, hPC⟩
  obtain ⟨hAP, hAbig⟩ := mem_filter.mp hAC
  have hsub : A ⊆ P := mem_powerset.mp hAP
  have hne : A.Nonempty := by
    by_contra hnot
    rw [not_nonempty_iff_eq_empty.mp hnot, prod_empty, Nat.cast_one] at hAbig
    linarith
  obtain ⟨a, ha⟩ := hne
  have herase : ((A.erase a).prod id : ℕ) ≤ N := by
    by_contra hnot
    have hc : A.erase a ∈ C := mem_filter.mpr
      ⟨mem_powerset.mpr ((erase_subset a A).trans hsub), lt_of_not_ge hnot⟩
    exact (not_lt_of_ge (hmin _ hc)) (card_erase_lt_of_mem ha)
  refine ⟨A, hsub, hAbig, ?_⟩
  calc
    _ = (a : ℝ) * ((A.erase a).prod id : ℕ) := by rw [← mul_prod_erase A id ha, Nat.cast_mul]; rfl
    _ ≤ Z * N := mul_le_mul (hupper a (hsub ha)) herase (Nat.cast_nonneg _) hZ
    _ = _ := mul_comm _ _

theorem large_factor_card (P : Finset ℕ) (N : ℝ) (hN : 1 ≤ N) (k : ℕ) (hk : 1 ≤ k)
    (hselected : ∀ A ⊆ P, A.card = k → (A.prod id : ℕ) ≤ N) :
    (P.filter fun g : ℕ ↦ N ^ (1 / (k : ℝ)) < (g : ℝ)).card ≤ k - 1 := by
  classical
  let Q := P.filter fun g : ℕ ↦ N ^ (1 / (k : ℝ)) < (g : ℝ)
  by_contra hnot
  change ¬ Q.card ≤ k - 1 at hnot
  have hcard : k ≤ Q.card := by omega
  obtain ⟨A, hAQ, hAk⟩ := exists_subset_card_eq hcard
  have hAP : A ⊆ P := hAQ.trans (filter_subset _ _)
  have hroot : 0 < N ^ (1 / (k : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
  have hbig : (N ^ (1 / (k : ℝ))) ^ k < (A.prod id : ℕ) := by
    calc
      _ = ∏ _g ∈ A, N ^ (1 / (k : ℝ)) := by rw [prod_const, hAk]
      _ < ∏ g ∈ A, (g : ℝ) := prod_lt_prod_of_nonempty₀
        (fun _ _ ↦ hroot) (fun g hg ↦ (mem_filter.mp (hAQ hg)).2) (card_pos.mp (by omega))
      _ = _ := by simp only [Nat.cast_prod, id_eq]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have heq : (N ^ (1 / (k : ℝ))) ^ k = N := by
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ N)]
    rw [one_div_mul_cancel hkpos.ne', Real.rpow_one]
  rw [heq] at hbig
  exact (not_lt_of_ge (hselected A hAP hAk)) hbig

theorem confinement_or_certificate (P : Finset ℕ) (Y N : ℝ) (hY : 1 < Y) (hN : 1 ≤ N)
    (k : ℕ) (hk : 1 ≤ k) (hP : ∀ g ∈ P, Y < (g : ℝ))
    (hselected : ∀ A ⊆ P, A.card = k → (A.prod id : ℕ) ≤ N) :
    P.card ≤ k - 1 + ⌊Real.log N / Real.log Y⌋₊ ∨
      ∃ A ⊆ P, (∀ g ∈ A, (g : ℝ) ≤ N ^ (1 / (k : ℝ))) ∧
        N < (A.prod id : ℕ) ∧ (A.prod id : ℕ) ≤ N ^ (1 + 1 / (k : ℝ)) := by
  classical
  let huge := P.filter fun g : ℕ ↦ N ^ (1 / (k : ℝ)) < (g : ℝ)
  let small := P \ huge
  have hhuge : huge.card ≤ k - 1 := large_factor_card P N hN k hk hselected
  have hsmall : small ⊆ P := sdiff_subset
  have hbound (g : ℕ) (hg : g ∈ small) : (g : ℝ) ≤ N ^ (1 / (k : ℝ)) := by
    obtain ⟨hgP, hgH⟩ := mem_sdiff.mp hg
    by_contra hnot
    exact hgH (mem_filter.mpr ⟨hgP, lt_of_not_ge hnot⟩)
  by_cases hprod : (small.prod id : ℕ) ≤ N
  · left
    have hlog := card_le_log small Y N hY (fun g hg ↦ hP g (hsmall hg)) hprod
    have hcard : P.card = huge.card + small.card := by
      have hsub : huge ⊆ P := filter_subset _ _
      dsimp only [small]
      rw [card_sdiff_of_subset hsub]
      have hc := card_le_card hsub
      omega
    omega
  · right
    obtain ⟨A, hAs, hAlo, hAhi⟩ := stopping_subset small N (N ^ (1 / (k : ℝ))) hN
      (Real.rpow_nonneg (by linarith) _) hbound (lt_of_not_ge hprod)
    refine ⟨A, hAs.trans hsmall, fun g hg ↦ hbound g (hAs hg), hAlo, ?_⟩
    have hn : 0 < N := by linarith
    calc
      _ ≤ N * N ^ (1 / (k : ℝ)) := hAhi
      _ = _ := by rw [Real.rpow_add hn, Real.rpow_one]

end PaperP1.ProductConfinement
