module

public import PaperP1.Arithmetic.DeterminantSourceBox
public import PaperP1.Asymptotics.LocalDeterminantAuxiliary

/-! # Actual source boxes admit uniformly bounded auxiliary curves on every occupied chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantBoxAuxiliary

open Finset PaperP1.DeterminantSourceBox PaperP1.TwoKernelDeterminantBoxes
  PaperP1.DeterminantIntegerRows PaperP1.DeterminantRelativeIntervals
  PaperP1.DeterminantIntervalPartition PaperP1.DeterminantRelativeChart
  PaperP1.DeterminantFixedInflation PaperP1.DeterminantHorizontalScale
  PaperP1.DeterminantNormalizedWeights PaperP1.DeterminantAuxiliaryBiform
  PaperP1.ActualRelativeDeterminant

theorem uniform_biforms (δ C ρ Kshift A₀ ζ : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hζ : 0 < ζ) (hζsmall : ζ < 7 / 16) :
    ∃ B Amax κ N₀ : ℕ, 0 < B ∧ ∀ N ≥ N₀, ∀ h : ℕ,
      0 < h → (h : ℝ) ≤ Kshift * (Real.log N) ^ A₀ →
      ∀ X : Box N ρ C δ, ∀ S : Finset Quad, Population X h S →
      let M := horizontalScale N X.D X.E X.U X.V ζ
      4 ≤ M ∧ S.card = ∑ k ∈ intervalIndices M, (cluster M X.D X.E k S).card ∧
      ∀ k ∈ intervalIndices M, (cluster M X.D X.E k S).Nonempty →
        ∃ A : ℕ, 0 < A ∧ A ≤ Amax ∧ ∃ w : Exponent A B → ℤ,
          biform A B w ≠ 0 ∧ (biform A B w).IsHomogeneous A ∧
          (∀ a, (forms A B w a).IsHomogeneous B) ∧
          (∀ m n, |((biform A B w).coeff m).coeff n| ≤ ((N ^ κ : ℕ) : ℤ)) ∧
          ∀ p ∈ cluster M X.D X.E k S,
            MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1])
              ![(p.1.1 : ℤ), p.1.2] (biform A B w) = 0 := by
  let K := inflation ρ C
  have hK : 0 < K := div_pos (mul_pos (by norm_num) hC) hρ
  obtain ⟨η, hη, _, Nw, hweights⟩ := DeterminantSourceWeightMargin.uniform_margin δ 3 (K ^ 3)
    Kshift A₀ ζ ρ hδ (by norm_num) (pow_pos hK _) hζ hρ hρ₁
  let Q := ⌈2 * C⌉₊ + 1
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hQr : 2 * C ≤ (Q : ℝ) := by
    have hh := Nat.le_ceil (2 * C)
    dsimp [Q]
    push_cast
    linarith only [hh]
  obtain ⟨B, Amax, κ, Na, hB, haux⟩ := LocalDeterminantAuxiliary.uniform_biform δ 4 2 η hδ hη Q hQ
  obtain ⟨Nm, hm⟩ := uniform_admissible C ζ Kshift A₀ hC hζ.le hζsmall
  obtain ⟨Nb, hb⟩ := DeterminantBoxScales.uniform_base_logs C hC
  obtain ⟨N4, h4⟩ := fixed_log_error 4 (ζ / 2) (by positivity)
  let N₀ := max 2 (max Na (max Nw (max Nm (max Nb N4))))
  refine ⟨B, Amax, κ, N₀, hB, ?_⟩
  intro N hN h hh hshift X S hS
  have hN₂ : 2 ≤ N := by dsimp [N₀] at hN; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hc₁ : 0 < X.c₁ := by linarith only [X.c₁_ge_one]
  have hc₂ : 0 < X.c₂ := by linarith only [X.c₂_ge_one]
  have hD : 0 < X.D := by linarith only [X.D_ge_one]
  have hE : 0 < X.E := by linarith only [X.E_ge_one]
  have hU : 0 < X.U := by linarith only [X.U_ge_one]
  have hV : 0 < X.V := by linarith only [X.V_ge_one]
  have hcoeff : 1 ≤ X.c₁ * X.c₂ := by
    nlinarith only [X.c₁_ge_one, X.c₂_ge_one,
      mul_nonneg (sub_nonneg.mpr X.c₁_ge_one) (sub_nonneg.mpr X.c₂_ge_one)]
  have hDE : 1 ≤ X.D * X.E := by
    nlinarith only [X.D_ge_one, X.E_ge_one,
      mul_nonneg (sub_nonneg.mpr X.D_ge_one) (sub_nonneg.mpr X.E_ge_one)]
  let M := horizontalScale N X.D X.E X.U X.V ζ
  obtain ⟨hMp, hMh, _⟩ := hm N (by dsimp [N₀] at hN; omega) h hh hshift
    X.c₁ X.c₂ X.D X.E X.U X.V hc₁ hc₂ hD hE hU hV hcoeff hDE X.first_upper X.second_upper
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hmR : (M : ℝ) ≤ N := by
    have hhM := mul_le_mul_of_nonneg_left hhR (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    nlinarith only [hhM, hMh]
  have hMN : M ≤ N := by exact_mod_cast hmR
  have hscale := horizontalScale_lower N X.D X.E X.U X.V ζ
  have hlog4 := (h4 N (by dsimp [N₀] at hN; omega)).2
  have hlo := horizontal_lower N M hN₂ hMp X.D X.E X.U X.V ζ hscale
  have hbase₁ : 0 ≤ Real.log (X.D * X.E) / Real.log N :=
    div_nonneg ((mul_pos hδ ht).trans_le X.first_log).le ht.le
  have hbase₂ : 0 ≤ Real.log (X.U * X.V) / Real.log N :=
    div_nonneg ((mul_pos hδ ht).trans_le X.second_log).le ht.le
  have hσ : 0 < horizontal N M := by
    have hp : 0 ≤ (9 / 8 : ℝ) * (Real.log (X.D * X.E) / Real.log N) *
        (Real.log (X.U * X.V) / Real.log N) := by positivity
    linarith only [hlo, hlog4, hp, hζ]
  have hMlog : 0 < Real.log ((M : ℝ) / 4) := by
    have hp := mul_pos hσ ht
    change 0 < (Real.log ((M : ℝ) / 4) / Real.log N) * Real.log N at hp
    rwa [div_mul_cancel₀ _ ht.ne'] at hp
  have hM₄ : 4 ≤ M := by
    have hp := (Real.log_pos_iff (show (0 : ℝ) ≤ (M : ℝ) / 4 by positivity)).mp hMlog
    have hm4 : (4 : ℝ) < M := by linarith only [hp]
    have hn4 : 4 < M := by exact_mod_cast hm4
    omega
  obtain ⟨_, hDEupper, hUVupper⟩ := hb N (by dsimp [N₀] at hN; omega)
    X.c₁ X.c₂ X.D X.E X.U X.V X.c₁_ge_one X.c₂_ge_one X.D_ge_one X.E_ge_one X.U_ge_one X.V_ge_one
    X.first_upper X.second_upper
  have hK₁ : 1 ≤ K := by
    have ho := source_comparisons_order hn X.first_lower X.first_upper
    have hg := inflation_ge_sixteen hρ ho
    linarith only [hg]
  have hheight := population_height X S hS hQr
  refine ⟨hM₄, finite_partition M hM₄ hD hE S (fun p hp ↦
    ⟨(hS.d_bounds p hp).1, (hS.d_bounds p hp).2, (hS.e_bounds p hp).1, (hS.e_bounds p hp).2⟩), ?_⟩
  intro k hk hnonempty
  obtain ⟨p₀, hp₀⟩ := hnonempty
  have hp₀S := ((mem_cluster M X.D X.E k S p₀).mp hp₀).1
  have hcenter := point_center_bounds M hM₄ hD hE S p₀ k hp₀
    (hS.d_bounds p₀ hp₀S).1 (hS.d_bounds p₀ hp₀S).2 (hS.e_bounds p₀ hp₀S).1 (hS.e_bounds p₀ hp₀S).2
  let s₀ := intervalCenter M X.D X.E k
  have hs₀ : 0 < s₀ := (div_pos hD (by positivity : 0 < 4 * X.E)).trans_le hcenter.1
  have heffective := effective_products hc₂ hD hE hU hV hn hρ hC X.first_lower X.first_upper
    X.second_lower X.second_upper hcenter.1 hcenter.2
  obtain ⟨_, ha₀, haC, hb₀, hbC, hσp, hτp, hsum, hproduct⟩ := hweights N
    (by dsimp [N₀] at hN; omega) M h X.D X.E X.U X.V
    ((2 * X.E) ^ 2 * s₀) ((K * X.U) ^ 2 * center X.c₁ X.c₂ s₀)
    hMp hMN hD hE hU hV hhR hshift hscale X.first_log hDEupper X.second_log hUVupper
    heffective.1.1 heffective.1.2 heffective.2.1 heffective.2.2
  let Y : DeterminantLocalChart.Data (Real.log N) δ 4 2 η := {
    E := 2 * X.E, U := K * X.U, c₁ := X.c₁, c₂ := X.c₂, h := h, s₀ := s₀
    a := Real.log ((2 * X.E) ^ 2 * s₀) / Real.log N
    b := Real.log ((K * X.U) ^ 2 * center X.c₁ X.c₂ s₀) / Real.log N
    σ := horizontal N M, τ := vertical N ρ h
    E_pos := by positivity, U_pos := mul_pos hK hU, c₁_pos := hc₁, c₂_pos := hc₂, s₀_pos := hs₀
    first_log := (div_mul_cancel₀ _ ht.ne').symm, second_log := (div_mul_cancel₀ _ ht.ne').symm
    first_lower := ha₀, first_upper := by linarith only [haC]
    second_lower := hb₀, second_upper := by linarith only [hbC]
    horizontal_pos := hσp, vertical_pos := hτp, weight_sum := hsum, weight_product := hproduct }
  obtain ⟨A, hA₀, hA, hcurve⟩ := haux N (by dsimp [N₀] at hN; omega) Y
  refine ⟨A, hA₀, hA, ?_⟩
  apply hcurve (cluster M X.D X.E k S)
  refine { height := ?_, e_pos := ?_, u_pos := ?_, e_bound := ?_, u_bound := ?_, equation := ?_, horizontal := ?_, vertical := ?_ }
  all_goals intro p hp
  all_goals have hpS := ((mem_cluster M X.D X.E k S p).mp hp).1
  · exact hheight p hpS
  · exact (population_denominators_positive X S hS p hpS).1
  · exact (population_denominators_positive X S hS p hpS).2
  · exact (hS.e_bounds p hpS).2
  · have hu := (hS.u_bounds p hpS).2
    have hK₂ : 2 ≤ K := by
      have ho := source_comparisons_order hn X.first_lower X.first_upper
      have hg := inflation_ge_sixteen hρ ho
      linarith only [hg]
    exact hu.trans (mul_le_mul_of_nonneg_right hK₂ hU.le)
  · exact hS.equation p hpS
  · change |relativeAlpha s₀ p| ≤ Real.exp (-(horizontal N M * Real.log N))
    rw [horizontal_error_scale N M hN₂ hMp]
    exact point_alpha_bound M hM₄ hD hE S p k hp
      (hS.d_bounds p hpS).1 (hS.d_bounds p hpS).2 (hS.e_bounds p hpS).1 (hS.e_bounds p hpS).2
  · change |relativeError X.c₁ X.c₂ (h : ℝ) s₀ p| ≤ Real.exp (-(vertical N ρ h * Real.log N))
    rw [vertical_error_scale N hN₂ hρ (by exact_mod_cast hh)]
    have hv := point_vertical_bound (h := (h : ℝ)) M hM₄ hD hE S p k hp
      (hS.d_bounds p hpS).1 (hS.d_bounds p hpS).2 (hS.e_bounds p hpS).1 (hS.e_bounds p hpS).2
      hc₁ hc₂ (population_denominators_positive X S hS p hpS).2 hn hρ (population_source_lower X S hS p hpS)
    simpa only [s₀, abs_of_nonneg (Nat.cast_nonneg h : (0 : ℝ) ≤ h)] using hv

end PaperP1.DeterminantBoxAuxiliary
