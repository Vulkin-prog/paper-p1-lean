module

public import PaperP1.Asymptotics.OriginalParticipatingTail
public import PaperP1.Asymptotics.RelativeOriginalWindowMass

/-! # All nontrivial participating original families have independent heterogeneous mass at most N^(-1+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalParticipatingMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

theorem fixed_mass (r : ℕ) (C M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ p : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x ∈ dyadicBlock N, p x ≤ M / N) →
      ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = r ∧ RelativeWindowFamilies.Witnesses L ⊥ I) →
      (∑ I ∈ F, ∏ x ∈ I, p x) ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NR, _hNR, hr⟩ := RelativeOriginalWindowMass.uniform_mass r 0 C (ε / 2) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (M ^ r) (-(r : ℝ) / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 3 (max NR NA), by omega, ?_⟩
  intro N hN L hband p hp hcap F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsub : F ⊆ RelativeWindowFamilies.families (dyadicBlock N) L r ⊥ := by
    intro I hI
    obtain ⟨hIG, hcard, hw⟩ := hF I hI
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hIG, hcard⟩, hw⟩
  have hcount : (F.card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε / 2) :=
    (show (F.card : ℝ) ≤ (RelativeWindowFamilies.families (dyadicBlock N) L r ⊥).card by
      exact_mod_cast card_le_card hsub).trans
      (hr N (by omega) L hband (Fin.elim0 : Fin 0 → ℕ) (fun i ↦ Fin.elim0 i) ⊥ bot_le
        (dyadicBlock N) (subset_refl _)).1
  calc
    _ ≤ (F.card : ℝ) * (M / N) ^ r := by
      calc
        _ ≤ ∑ _I ∈ F, (M / N) ^ r := by
          apply sum_le_sum
          intro I hI
          have hprod : (∏ x ∈ I, p x) ≤ ∏ _x ∈ I, M / N :=
            prod_le_prod₀ (fun x _ ↦ hp x) (fun x hx ↦ hcap x ((hF I hI).1 hx))
          simpa only [prod_const, (hF I hI).2.1] using hprod
        _ = _ := by simp
    _ ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε / 2) * (M / N) ^ r :=
      mul_le_mul_of_nonneg_right hcount (pow_nonneg (div_nonneg hM hn.le) _)
    _ = M ^ r * ((N : ℝ) ^ ((r : ℝ) / 2 + ε / 2) / (N : ℝ) ^ r) := by rw [div_pow]; ring
    _ = M ^ r * (N : ℝ) ^ (((r : ℝ) / 2 + ε / 2) - r) := by rw [Real.rpow_sub hn, Real.rpow_natCast]
    _ = M ^ r * (N : ℝ) ^ (-(r : ℝ) / 2 + ε / 2) := by congr 2; ring
    _ ≤ (N : ℝ) ^ ((-(r : ℝ) / 2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_mass (C M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ p : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x ∈ dyadicBlock N, p x ≤ M / N) →
      ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 2 ≤ I.card ∧ RelativeWindowFamilies.Witnesses L ⊥ I) →
      (∑ I ∈ F, ∏ x ∈ I, p x) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨s, _hs, NT, _hNT, ht⟩ := OriginalParticipatingTail.subcritical_tail C M 1 (ε / 4)
    hM (by norm_num) (by positivity)
  have hfixed (r : Fin s) := fixed_mass r.val C M (ε / 4) hM (by positivity)
  choose NR hNR hr using hfixed
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption ((s : ℝ) + 1) (-1 + ε / 4)
    (3 * ε / 4) (by positivity)
  refine ⟨10 + NT + NA + univ.sup NR, by omega, ?_⟩
  intro N hN L hband p hp hcap F hF
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let FS := F.filter fun I ↦ I.card < s
  let FT := F.filter fun I ↦ ¬ I.card < s
  have htail : (∑ I ∈ FT, ∏ x ∈ I, p x) ≤ (N : ℝ) ^ (-1 + ε / 4) :=
    ht N (by omega) L hband p hp hcap FT (by
      intro I hI
      obtain ⟨hIF, hsize⟩ := mem_filter.mp hI
      exact ⟨(hF I hIF).1, by omega, (hF I hIF).2.2⟩)
  have hsmall : (∑ I ∈ FS, ∏ x ∈ I, p x) ≤ (s : ℝ) * (N : ℝ) ^ (-1 + ε / 4) := by
    have hsplit := sum_fiberwise_of_maps_to (s := FS) (t := range s)
      (g := fun I : Finset ℕ ↦ I.card) (fun _ hI ↦ mem_range.mpr (mem_filter.mp hI).2)
      (fun I ↦ ∏ x ∈ I, p x)
    calc
      _ = ∑ r ∈ range s, ∑ I ∈ FS.filter (fun I ↦ I.card = r), ∏ x ∈ I, p x := hsplit.symm
      _ ≤ ∑ _r ∈ range s, (N : ℝ) ^ (-1 + ε / 4) := by
        apply sum_le_sum
        intro r hmem
        by_cases htwo : 2 ≤ r
        · let i : Fin s := ⟨r, mem_range.mp hmem⟩
          have hNi : NR i ≤ univ.sup NR := le_sup (f := NR) (mem_univ i)
          have hbound := hr i N (by omega) L hband p hp hcap (FS.filter (fun I ↦ I.card = r)) (by
            intro I hI
            obtain ⟨hIS, hcard⟩ := mem_filter.mp hI
            have hIF := (mem_filter.mp hIS).1
            exact ⟨(hF I hIF).1, hcard, (hF I hIF).2.2⟩)
          exact hbound.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by
            have htwoR : (2 : ℝ) ≤ r := by exact_mod_cast htwo
            change -(r : ℝ) / 2 + ε / 4 ≤ -1 + ε / 4
            linarith only [htwoR]))
        · have hempty : FS.filter (fun I ↦ I.card = r) = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            intro I hI
            obtain ⟨hIS, hcard⟩ := mem_filter.mp hI
            have h := (hF I (mem_filter.mp hIS).1).2.1
            omega
          rw [hempty, sum_empty]
          exact Real.rpow_nonneg (Nat.cast_nonneg N) _
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  calc
    _ = (∑ I ∈ FS, ∏ x ∈ I, p x) + ∑ I ∈ FT, ∏ x ∈ I, p x :=
      (sum_filter_add_sum_filter_not F (fun I ↦ I.card < s) _).symm
    _ ≤ (s : ℝ) * (N : ℝ) ^ (-1 + ε / 4) + (N : ℝ) ^ (-1 + ε / 4) := add_le_add hsmall htail
    _ = ((s : ℝ) + 1) * (N : ℝ) ^ (-1 + ε / 4) := by ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 4) + 3 * ε / 4) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.OriginalParticipatingMass
