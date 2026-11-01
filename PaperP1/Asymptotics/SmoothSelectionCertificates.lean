module

public import PaperP1.Arithmetic.LargeSmoothCertificates
public import PaperP1.Asymptotics.TwoSmallKernelCount

/-! # Actual large smooth certificates from a constant-size selected family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothSelectionCertificates

open Finset PaperP1.SmallPrimeBudget PaperP1.LinearKernelFibres
  PaperP1.LargeOddKernel PaperP1.SmoothModulusHosts PaperP1.DefectivePredicate

def lowerConstant (C : ℕ) : ℝ := 1 / (2 * C)

theorem value_bounds (C N n W : ℕ) (a : ℤ) (hC : 1 ≤ C) (hN : 0 < N)
    (hW : 2 * C * W ≤ N) (hlo : N ≤ C * n) (hhi : n ≤ C * N) (ha : a.natAbs ≤ W) :
    W < n ∧ 0 < value n a ∧ lowerConstant C * N ≤ value n a ∧
      (value n a : ℝ) ≤ (C + 1 : ℝ) * N := by
  have hCp : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hnp : 0 < n := by nlinarith only [hlo, hN]
  have hWn : W < n := by
    by_contra hnot
    have hmul := Nat.mul_le_mul_left C (le_of_not_gt hnot)
    nlinarith only [hW, hlo, hmul, hN, hnp, hC]
  have hval := value_cast n W a hWn ha
  have habs : |a| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ha
  have hab := abs_le.mp habs
  have hnW : (W : ℤ) < n := by exact_mod_cast hWn
  have hvp : 0 < value n a := by omega
  have hvlo : (n : ℝ) - W ≤ value n a := by
    have h : (n : ℤ) - W ≤ (value n a : ℤ) := by omega
    exact_mod_cast h
  have hvhi : (value n a : ℝ) ≤ (n : ℝ) + W := by
    have h : (value n a : ℤ) ≤ (n : ℤ) + W := by omega
    exact_mod_cast h
  have hWreal : 2 * (C : ℝ) * W ≤ N := by exact_mod_cast hW
  have hloreal : (N : ℝ) ≤ (C : ℝ) * n := by exact_mod_cast hlo
  have hhireal : (n : ℝ) ≤ (C : ℝ) * N := by exact_mod_cast hhi
  have hlow : (N : ℝ) / (2 * C) ≤ value n a := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * C)).mpr
    nlinarith only [hWreal, hloreal, hvlo]
  have hWNr : (W : ℝ) ≤ N := by
    have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
    nlinarith only [hWreal, hC1, (show (0 : ℝ) ≤ W from Nat.cast_nonneg W)]
  refine ⟨hWn, hvp, ?_, ?_⟩
  · simpa only [lowerConstant, div_eq_mul_inv, one_mul, mul_comm] using hlow
  · nlinarith only [hvhi, hhireal, hWNr]

theorem square_budget (C : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((C + 1 : ℝ) * N) ^ 2 ≤ (N : ℝ) ^ (1 / 2 : ℝ) * ((N : ℝ) ^ (19 / 25 : ℝ)) ^ 2 := by
  obtain ⟨N₀, hN₀⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow
    ((C + 1 : ℝ) ^ 2) 0 (1 / 50) (by norm_num)
  refine ⟨max 2 N₀, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : (C + 1 : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 / 50 : ℝ) := by
    simpa only [Real.rpow_zero, mul_one] using hN₀ N (by omega)
  calc
    _ = (C + 1 : ℝ) ^ 2 * (N : ℝ) ^ 2 := mul_pow _ _ _
    _ ≤ (N : ℝ) ^ (1 / 50 : ℝ) * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hp (sq_nonneg _)
    _ = _ := by
      rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_natCast, ← Real.rpow_add hn, ← Real.rpow_add hn]
      norm_num

theorem product_budget (C : ℕ) (hC : 1 ≤ C) (E A₀ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, 0 < W → (W : ℝ) ≤ E * (Real.log N) ^ A₀ →
      (C : ℝ) * N * (2 * W : ℝ) ^ (26 ^ 2 : ℕ) <
        (lowerConstant C * (N : ℝ) ^ (1 / 25 : ℝ)) ^ (26 : ℕ) := by
  let α := lowerConstant C
  have hα : 0 < α := by dsimp [α, lowerConstant]; positivity
  let K := (C + 1 : ℝ) * (2 * E) ^ (26 ^ 2 : ℕ) / α ^ (26 : ℕ)
  obtain ⟨N₀, hN₀⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow K
    (A₀ * (26 ^ 2 : ℕ)) (1 / 25) (by norm_num)
  refine ⟨max 2 N₀, ?_⟩
  intro N hN W hW hwidth
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hw : (2 * W : ℝ) ≤ 2 * E * (Real.log N) ^ A₀ := by nlinarith only [hwidth]
  have hwpow : (2 * W : ℝ) ^ (26 ^ 2 : ℕ) ≤ (2 * E) ^ (26 ^ 2 : ℕ) *
      (Real.log N) ^ (A₀ * (26 ^ 2 : ℕ)) := by
    calc
      _ ≤ (2 * E * (Real.log N) ^ A₀) ^ (26 ^ 2 : ℕ) :=
        pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * W) hw (26 ^ 2 : ℕ)
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hl.le]
  have hpenalty : (C + 1 : ℝ) * (2 * W : ℝ) ^ (26 ^ 2 : ℕ) ≤ α ^ (26 : ℕ) * (N : ℝ) ^ (1 / 25 : ℝ) := by
    calc
      _ ≤ (C + 1 : ℝ) * ((2 * E) ^ (26 ^ 2 : ℕ) * (Real.log N) ^ (A₀ * (26 ^ 2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hwpow (by positivity)
      _ = α ^ (26 : ℕ) * (K * (Real.log N) ^ (A₀ * (26 ^ 2 : ℕ))) := by
        dsimp [K]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hN₀ N (by omega)) (by positivity)
  have hwpos : 0 < (2 * W : ℝ) ^ (26 ^ 2 : ℕ) := by positivity
  calc
    _ < (C + 1 : ℝ) * N * (2 * W : ℝ) ^ (26 ^ 2 : ℕ) :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (lt_add_one (C : ℝ)) hn) hwpos
    _ ≤ N * (α ^ (26 : ℕ) * (N : ℝ) ^ (1 / 25 : ℝ)) := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left hpenalty hn.le
    _ = α ^ (26 : ℕ) * ((N : ℝ) * (N : ℝ) ^ (1 / 25 : ℝ)) := by ring
    _ = α ^ (26 : ℕ) * (N : ℝ) ^ (1 + 1 / 25 : ℝ) := by
      congr 1
      calc
        _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 / 25 : ℝ) :=
          congrArg (fun x : ℝ ↦ x * (N : ℝ) ^ (1 / 25 : ℝ)) (Real.rpow_one _).symm
        _ = _ := (Real.rpow_add hn _ _).symm
    _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hn.le]; norm_num [α]

theorem source_certificates (C : ℕ) (hC : 1 ≤ C) (E A₀ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H Y W n t : ℕ, ∀ S : Finset ℤ,
      0 < W → (W : ℝ) ≤ E * (Real.log N) ^ A₀ → N ≤ C * n → n ≤ C * N →
      (∀ a ∈ S, a.natAbs ≤ W) → t + 26 ≤ S.card →
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → (N : ℝ) ^ (1 / 2 : ℝ) <
        (largeOddKernel H (value n a) : ℝ) * (largeOddKernel H (value n b) : ℝ)) →
      (S.filter fun a ↦ (N : ℝ) ^ (1 / 5 : ℝ) < (largeOddKernel Y (value n a) : ℝ)).card < t →
      W < n ∧ ∃ m : ℕ, (C * N : ℕ) < m ∧ (m : ℝ) ≤ (C : ℝ) * N * Y ∧ Squarefree m ∧ largeOddKernel Y m = 1 ∧
        HasCertificate (ι := Fin 26) m W n := by
  classical
  obtain ⟨Nw, hNw⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow
    (2 * C * E) A₀ 1 (by norm_num)
  obtain ⟨Ns, hNs⟩ := square_budget C
  obtain ⟨Np, hNp⟩ := product_budget C hC E A₀
  refine ⟨max 2 (max Nw (max Ns Np)), ?_⟩
  intro N hN H Y W n t S hW hwidth hnlo hnhi hS hcard hpair hlarge
  have hnN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hWNr : 2 * (C : ℝ) * W ≤ N := by
    have hw := hNw N (by omega)
    rw [Real.rpow_one] at hw
    have hm := mul_le_mul_of_nonneg_left hwidth (by positivity : (0 : ℝ) ≤ 2 * C)
    nlinarith only [hm, hw]
  have hWN : 2 * C * W ≤ N := by exact_mod_cast hWNr
  have hv : ∀ a ∈ S, W < n ∧ 0 < value n a ∧ lowerConstant C * N ≤ value n a ∧
      (value n a : ℝ) ≤ (C + 1 : ℝ) * N :=
    fun a ha ↦ value_bounds C N n W a hC (by omega) hWN hnlo hnhi (hS a ha)
  have hsquare : (S.filter fun a ↦ (N : ℝ) ^ (19 / 25 : ℝ) < (canonicalSquarePart (value n a) : ℝ) ^ 2).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨haS, haL⟩ := mem_filter.mp ha
    obtain ⟨hbS, hbL⟩ := mem_filter.mp hb
    by_contra hab
    have hbound := PaperP1.KernelSquareBudget.pair_bound H (value n a) (value n b)
      ((N : ℝ) ^ (19 / 25 : ℝ)) ((C + 1 : ℝ) * N) ((N : ℝ) ^ (1 / 2 : ℝ))
      (Real.rpow_pos_of_pos hnN _) (by positivity) (hv a haS).2.1 (hv b hbS).2.1
      (hv a haS).2.2.2 (hv b hbS).2.2.2 haL.le hbL.le (hNs N (by omega))
    exact (not_lt_of_ge hbound) (hpair a haS b hbS hab)
  let G := S.filter fun a ↦ (canonicalSquarePart (value n a) : ℝ) ^ 2 ≤ (N : ℝ) ^ (19 / 25 : ℝ) ∧
    (largeOddKernel Y (value n a) : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ)
  have hGcard : 26 ≤ G.card := PaperP1.KernelSquareBudget.good_values_card S (value n) Y t 26
    ((N : ℝ) ^ (19 / 25 : ℝ)) ((N : ℝ) ^ (1 / 5 : ℝ)) hcard hsquare hlarge
  obtain ⟨T, hTG, hTcard⟩ := exists_subset_card_eq hGcard
  let e : Fin 26 ≃ T := (Finset.equivFinOfCardEq hTcard).symm
  let a : Fin 26 → ℤ := fun i ↦ (e i).val
  have haG : ∀ i, a i ∈ G := fun i ↦ hTG (e i).property
  have haS : ∀ i, a i ∈ S := fun i ↦ (mem_filter.mp (haG i)).1
  have ha : ∀ i, (a i).natAbs ≤ W := fun i ↦ hS (a i) (haS i)
  have hinj : Function.Injective a := fun i j hij ↦ e.injective (Subtype.ext hij)
  have hsmall : ∀ i, lowerConstant C * (N : ℝ) ^ (1 / 25 : ℝ) ≤ smallOddPart Y (value n (a i)) := by
    intro i
    have hi := (mem_filter.mp (haG i)).2
    exact PaperP1.KernelSquareBudget.smooth_part_lower Y _ N (lowerConstant C) hnN
      (hv (a i) (haS i)).2.1 (hv (a i) (haS i)).2.2.1 hi.1 hi.2
  have hprodlower : (lowerConstant C * (N : ℝ) ^ (1 / 25 : ℝ)) ^ (26 : ℕ) ≤
      ∏ i : Fin 26, (smallOddPart Y (value n (a i)) : ℝ) := by
    calc
      _ = ∏ _i : Fin 26, lowerConstant C * (N : ℝ) ^ (1 / 25 : ℝ) := by simp only [prod_const, card_univ, Fintype.card_fin]
      _ ≤ _ := prod_le_prod₀ (fun _ _ ↦ by dsimp [lowerConstant]; positivity) (fun i _ ↦ hsmall i)
  have hbig := (hNp N (by omega) W hW hwidth).trans_le hprodlower
  have hX : (1 : ℝ) ≤ (C : ℝ) * N := by
    have hNpos : 1 ≤ N := by omega
    exact_mod_cast Nat.mul_le_mul hC hNpos
  have hWn := (hv (a 0) (haS 0)).1
  obtain ⟨m, hmlo, hmhi, hmSF, hmK, hmcert⟩ := PaperP1.LargeSmoothCertificates.exists_certificate
    Y n W a ((C : ℝ) * N) hW hWn ha hinj hX (by simpa only [Fintype.card_fin] using hbig)
  exact ⟨hWn, m, by exact_mod_cast hmlo, hmhi, hmSF, hmK, hmcert⟩

end PaperP1.SmoothSelectionCertificates
