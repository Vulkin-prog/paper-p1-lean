module

public import PaperP1.Asymptotics.FixedPrimitiveMassUnderInputs
public import PaperP1.Asymptotics.WeightedPrimitiveTail
public import PaperP1.Model.RetainedReferenceTheorem

/-! # All-cardinality primitive joint and centered mass has the stronger power one under the recorded finite geometry -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPrimitiveMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies PaperP1.WeightedPrimitiveMass PaperP1.DensePrimitiveTripleMassUnderInputs

theorem weighted_fixed (r : ℕ) (hr : 3 ≤ r) (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p → ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = r ∧ Primitive L I) →
      rankMass F L u ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨p, hp⟩ := FixedPrimitiveMassUnderInputs.uniform_fixed r hr C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (u ^ r) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NM, _hNM, hm⟩ := hp hgeo
  refine ⟨3 + NM + NF, by omega, ?_⟩
  intro N hN L hband F hF
  calc
    _ = u ^ r * PrimitiveWindowMass.mass F L := fixed_weight F L r u (fun I hI ↦ (hF I hI).2.1)
    _ ≤ u ^ r * (N : ℝ) ^ (-1 + ε / 2) :=
      mul_le_mul_of_nonneg_left (hm N (by omega) L hband F hF) (pow_nonneg hu.le r)
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_rank (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ s : ℕ, 3 ≤ s ∧ ∃ p : Fin s → Parameters, (∀ i, Hypotheses (p i)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 3 ≤ I.card ∧ Primitive L I) →
        rankMass F L u ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨s, hs, NT, _hNT, ht⟩ := WeightedPrimitiveTail.uniform_tail u C (ε / 4) hu (by positivity)
  have hfixed (r : Fin s) := weighted_fixed (max 3 r.val) (le_max_left _ _) u C (ε / 4) hu (by positivity)
  choose p hp using hfixed
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption ((s : ℝ) + 1) (-1 + ε / 4) (3 * ε / 4) (by positivity)
  refine ⟨s, hs, p, ?_⟩
  intro hgeo
  have hthreshold (i : Fin s) := hp i (hgeo i)
  choose NR hNR hr using hthreshold
  refine ⟨10 + NT + NA + univ.sup NR, by omega, ?_⟩
  intro N hN L hband F hF
  let FS := F.filter fun I ↦ I.card < s
  let FT := F.filter fun I ↦ ¬ I.card < s
  have htail : rankMass FT L u ≤ (N : ℝ) ^ (-1 + ε / 4) := ht N (by omega) L hband FT (by
    intro I hI
    obtain ⟨hIF, hsize⟩ := mem_filter.mp hI
    exact ⟨(hF I hIF).1, by omega, (hF I hIF).2.2⟩)
  have hsmall : rankMass FS L u ≤ (s : ℝ) * (N : ℝ) ^ (-1 + ε / 4) := by
    have hsplit := sum_fiberwise_of_maps_to (s := FS) (t := range s) (g := fun I : Finset ℕ ↦ I.card)
      (fun _ hI ↦ mem_range.mpr (mem_filter.mp hI).2)
      (fun I ↦ u ^ I.card * PrimitiveWindowMass.weight L I)
    calc
      _ = ∑ r ∈ range s, rankMass (FS.filter (fun I ↦ I.card = r)) L u := hsplit.symm
      _ ≤ ∑ _r ∈ range s, (N : ℝ) ^ (-1 + ε / 4) := by
        apply sum_le_sum
        intro r hmem
        by_cases hthree : 3 ≤ r
        · let i : Fin s := ⟨r, mem_range.mp hmem⟩
          have hNi : NR i ≤ univ.sup NR := le_sup (f := NR) (mem_univ i)
          have hmax : max 3 i.val = r := max_eq_right hthree
          have hbound := hr i N (by omega) L hband (FS.filter (fun I ↦ I.card = r)) (by
            intro I hI
            obtain ⟨hIS, hcard⟩ := mem_filter.mp hI
            have hIF := (mem_filter.mp hIS).1
            exact ⟨(hF I hIF).1, hcard.trans hmax.symm, (hF I hIF).2.2⟩)
          exact hbound
        · have hempty : FS.filter (fun I ↦ I.card = r) = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            intro I hI
            obtain ⟨hIS, hcard⟩ := mem_filter.mp hI
            have h := (hF I (mem_filter.mp hIS).1).2.1
            omega
          rw [hempty, rankMass, sum_empty]
          exact Real.rpow_nonneg (Nat.cast_nonneg N) _
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  calc
    _ = rankMass FS L u + rankMass FT L u :=
      (sum_filter_add_sum_filter_not F (fun I ↦ I.card < s) (fun I ↦ u ^ I.card * PrimitiveWindowMass.weight L I)).symm
    _ ≤ ((s : ℝ) + 1) * (N : ℝ) ^ (-1 + ε / 4) := by linarith only [hsmall, htail]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 4) + 3 * ε / 4) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_actual (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ s : ℕ, 3 ≤ s ∧ ∃ p : Fin s → Parameters, (∀ i, Hypotheses (p i)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ RegularStarts.regularStarts N L →
        actualMass (families G L 3) L u ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨s, hs, p, hp⟩ := uniform_rank u C (ε / 2) hu (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨s, hs, p, ?_⟩
  intro hgeo
  obtain ⟨NR, _hNR, hr⟩ := hp hgeo
  refine ⟨10 + NG + NF + NR, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hdata : ∀ I ∈ families G L 3, I ⊆ dyadicBlock N ∧ 3 ≤ I.card ∧ Primitive L I := by
    intro I hI
    obtain ⟨hIG, hsize, hprim⟩ := (mem_families G I L 3).mp hI
    exact ⟨hIG.trans (hG.trans (RegularStarts.regularStarts_subset N L)), hsize, hprim⟩
  calc
    _ ≤ 2 * rankMass (families G L 3) L u := actual_le_rank _ L hL u hu.le (by
      intro I hI
      have hd := hdata I hI
      refine ⟨card_pos.mp (by omega), ?_⟩
      intro x hx
      rw [RetainedReferenceTheorem.ground_marginal (by omega : 2 ≤ N) hL x
        (hG (((mem_families G I L 3).mp hI).1 hx))]
      positivity)
    _ ≤ 2 * (N : ℝ) ^ (-1 + ε / 2) :=
      mul_le_mul_of_nonneg_left (hr N (by omega) L hband _ hdata) (by norm_num)
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem companion_T14_2 (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ s : ℕ, 3 ≤ s ∧ ∃ p : Fin s → Parameters, (∀ i, Hypotheses (p i)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        actualMass (families (RegularStarts.regularStarts N L) L 3) L u ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨s, hs, p, hp⟩ := uniform_actual u C ε hu hε
  refine ⟨s, hs, p, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, hh⟩ := hp hgeo
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  exact (hh N hN L hband _ Subset.rfl).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith))

end PaperP1.AllPrimitiveMassUnderInputs
