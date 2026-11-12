module

public import PaperP1.Asymptotics.FullSupportWeightedCount

/-! # V2 companion T13.1: one cutoff before every minimum support size

The independent participating tail is used once, near exponent two. The
finitely many lower cardinalities use their actual half-power bounds. The
threshold precedes the weight function, the family and its minimum size.
The nominal ordered-list specialization retains the exact factorial quotient.
No pure endpoint N^-2 or weighted rank-loss tail is asserted.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.UniformFullSupportCount

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FullSupportOrderedLists

theorem uniform_participating_mass (C M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ p : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x ∈ dyadicBlock N, p x ≤ M / N) →
      ∀ s : ℕ, 2 ≤ s → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ s ≤ I.card ∧ RelativeWindowFamilies.Witnesses L ⊥ I) →
      (∑ I ∈ F, ∏ x ∈ I, p x) ≤ (N : ℝ) ^ (-min ((s : ℝ) / 2) 2 + ε) := by
  classical
  obtain ⟨t, _ht, NT, _hNT, ht⟩ := OriginalParticipatingTail.subcritical_tail
    C M (2 - ε / 4) (ε / 4) hM (by linarith) (by positivity)
  let R := max 4 t
  have hfixed (r : Fin R) := OriginalParticipatingMass.fixed_mass r.val C M (ε / 4) hM (by positivity)
  choose NR hNR hr using hfixed
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption ((R : ℝ) + 1) 0 (ε / 2) (by positivity)
  refine ⟨10 + NT + NA + univ.sup NR, by omega, ?_⟩
  intro N hN L hband p hp hcap s hs F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let a := -min ((s : ℝ) / 2) 2
  let FS := F.filter fun I ↦ I.card < R
  let FT := F.filter fun I ↦ ¬ I.card < R
  have htail : (∑ I ∈ FT, ∏ x ∈ I, p x) ≤ (N : ℝ) ^ (a + ε / 2) := by
    have hb := ht N (by omega) L hband p hp hcap FT (by
      intro I hI
      obtain ⟨hIF, hsize⟩ := mem_filter.mp hI
      exact ⟨(hF I hIF).1, by dsimp [R] at *; omega, (hF I hIF).2.2⟩)
    apply hb.trans (Real.rpow_le_rpow_of_exponent_le hn1 ?_)
    dsimp [a]
    have hm := min_le_right ((s : ℝ) / 2) 2
    linarith only [hm]
  have hsmall : (∑ I ∈ FS, ∏ x ∈ I, p x) ≤ (R : ℝ) * (N : ℝ) ^ (a + ε / 2) := by
    have hsplit := sum_fiberwise_of_maps_to (s := FS) (t := range R)
      (g := fun I : Finset ℕ ↦ I.card) (fun _ hI ↦ mem_range.mpr (mem_filter.mp hI).2)
      (fun I ↦ ∏ x ∈ I, p x)
    calc
      _ = ∑ r ∈ range R, ∑ I ∈ FS.filter (fun I ↦ I.card = r), ∏ x ∈ I, p x := hsplit.symm
      _ ≤ ∑ _r ∈ range R, (N : ℝ) ^ (a + ε / 2) := by
        apply sum_le_sum
        intro r hmem
        by_cases hsr : s ≤ r
        · let i : Fin R := ⟨r, mem_range.mp hmem⟩
          have hNi : NR i ≤ univ.sup NR := le_sup (f := NR) (mem_univ i)
          have hb := hr i N (by omega) L hband p hp hcap (FS.filter (fun I ↦ I.card = r)) (by
            intro I hI
            obtain ⟨hIS, hcard⟩ := mem_filter.mp hI
            have hIF := (mem_filter.mp hIS).1
            exact ⟨(hF I hIF).1, hcard, (hF I hIF).2.2⟩)
          apply hb.trans (Real.rpow_le_rpow_of_exponent_le hn1 ?_)
          have hsrR : (s : ℝ) ≤ r := by exact_mod_cast hsr
          have hm := min_le_left ((s : ℝ) / 2) (2 : ℝ)
          change -(r : ℝ) / 2 + ε / 4 ≤ -min ((s : ℝ) / 2) 2 + ε / 2
          linarith only [hsrR, hm, hε]
        · have hempty : FS.filter (fun I ↦ I.card = r) = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            intro I hI
            obtain ⟨hIS, hcard⟩ := mem_filter.mp hI
            have h := (hF I (mem_filter.mp hIS).1).2.1
            omega
          rw [hempty, sum_empty]
          exact Real.rpow_nonneg hn.le _
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  have hfactor : (R : ℝ) + 1 ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using ha N (by omega)
  calc
    _ = (∑ I ∈ FS, ∏ x ∈ I, p x) + ∑ I ∈ FT, ∏ x ∈ I, p x :=
      (sum_filter_add_sum_filter_not F (fun I ↦ I.card < R) _).symm
    _ ≤ (R : ℝ) * (N : ℝ) ^ (a + ε / 2) + (N : ℝ) ^ (a + ε / 2) := add_le_add hsmall htail
    _ = ((R : ℝ) + 1) * (N : ℝ) ^ (a + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (a + ε / 2) :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; dsimp [a]; congr 1; ring

theorem uniform_ordered_mass (C u ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ s : ℕ, 2 ≤ s → orderedMass G L s (u * (2 ^ L : ℝ)⁻¹) ≤
        (N : ℝ) ^ (-min ((s : ℝ) / 2) 2 + ε) := by
  let M := u * (2 : ℝ) ^ C
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨N₀, hN₀, hm⟩ := uniform_participating_mass C M ε hM hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG s hs
  have hcap : ∀ x ∈ dyadicBlock N, u * (2 ^ L : ℝ)⁻¹ ≤ M / N := by
    intro _ _
    calc
      _ ≤ u * ((2 : ℝ) ^ C / N) := mul_le_mul_of_nonneg_left
        (LocalRigidityConsequences.nominal_marginal_bound (by omega) hband) hu.le
      _ = _ := by dsimp [M]; ring
  have hb := hm N hN L hband (fun _ ↦ u * (2 ^ L : ℝ)⁻¹) (fun _ ↦ by positivity)
    hcap s hs (IndependentFullSupportTail.families G L s) (by
      intro I hI
      obtain ⟨hIG, hsize, hfull⟩ := (IndependentFullSupportTail.mem_families G I L s).mp hI
      exact ⟨hIG.trans hG, hsize, IndependentFullSupportTail.witnesses L I hfull⟩)
  rw [ordered_mass_eq]
  simpa only [prod_const] using hb

theorem companion_T13_1 (C u ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ s : ℕ, 2 ≤ s →
      (∑ r ∈ Icc s G.card, (u ^ r / (r.factorial : ℝ)) *
        ((manuscriptLists G L r).card * ((2 ^ L : ℝ)⁻¹) ^ r)) ≤
          (N : ℝ) ^ (-min ((s : ℝ) / 2) 2 + ε) := by
  obtain ⟨N₀, hN₀, hm⟩ := uniform_ordered_mass C u ε hu hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG s hs
  have hb := hm N hN L hband G hG s hs
  rw [nominal_weight_formula] at hb
  apply le_trans _ hb
  apply sum_le_sum
  intro r _
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (by exact_mod_cast card_le_card (manuscriptLists_subset G L r)) (by positivity)) (by positivity)

end PaperP1.UniformFullSupportCount
