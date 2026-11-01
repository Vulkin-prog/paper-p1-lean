module

public import PaperP1.Asymptotics.TwoSmallKernelFibres
public import PaperP1.Combinatorics.BoundedIntegerMotifs
public import PaperP1.Asymptotics.ComparableSplitProductCount
public import PaperP1.Asymptotics.CriticalBandScale

/-! # Actual two-small-kernel centre counts, uniform in the product cap -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoSmallKernelCount

open Finset PaperP1.TwoSmallKernelFibres PaperP1.BoundedIntegerMotifs
  PaperP1.ComparableDyadicCover PaperP1.ComparableLogBounds

def HasPair (H W n : ℕ) (Q : ℝ) : Prop :=
  ∃ a b : ℤ, a.natAbs ≤ W ∧ b.natAbs ≤ W ∧ a ≠ b ∧
    (largeKernel H n a * largeKernel H n b : ℕ) ≤ Q

theorem dyadic_count (D E A₀ ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H W : ℕ, ∀ Q : ℝ,
      (H : ℝ) ≤ D * Real.log N → 0 < W → (W : ℝ) ≤ E * (Real.log N) ^ A₀ → 0 ≤ Q →
      ∀ S : Finset ℕ, (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ HasPair H W n Q) →
      (S.card : ℝ) ≤ Q * (N : ℝ) ^ ε := by
  obtain ⟨Nf, hNf⟩ := fixed_offsets D (ε / 2) hD (by positivity)
  obtain ⟨Nw, hNw⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow (2 * E) A₀ 1 (by norm_num)
  obtain ⟨No, hNo⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow (3 * E) A₀ (ε / 4) (by positivity)
  refine ⟨max 2 (max Nf (max Nw No)), ?_⟩
  intro N hN H W Q hH hW hwidth hQ S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hWN : 2 * W ≤ N := by
    have hw := hNw N (by omega)
    rw [Real.rpow_one] at hw
    have hw' : (2 * W : ℝ) ≤ N := by nlinarith only [hwidth, hw]
    exact_mod_cast hw'
  let I := ((offsets W) ×ˢ (offsets W)).filter fun w ↦ w.1 ≠ w.2
  let F := fun w : ℤ × ℤ ↦ S.filter fun n ↦
    (largeKernel H n w.1 * largeKernel H n w.2 : ℕ) ≤ Q
  have hcover : ∀ n ∈ S, ∃ w ∈ I, n ∈ F w := by
    intro n hnS
    obtain ⟨a, b, ha, hb, hab, hprod⟩ := (hS n hnS).2.2
    have ha' : a ∈ offsets W := (subset_offsets W {a}).mpr (by
      intro x hx; rwa [mem_singleton.mp hx]) (mem_singleton_self a)
    have hb' : b ∈ offsets W := (subset_offsets W {b}).mpr (by
      intro x hx; rwa [mem_singleton.mp hx]) (mem_singleton_self b)
    exact ⟨(a, b), mem_filter.mpr ⟨mem_product.mpr ⟨ha', hb'⟩, hab⟩,
      mem_filter.mpr ⟨hnS, hprod⟩⟩
  have hF : ∀ w ∈ I, ((F w).card : ℝ) ≤ Q * (N : ℝ) ^ (ε / 2) := by
    intro w hw
    obtain ⟨hwpool, hab⟩ := mem_filter.mp hw
    obtain ⟨ha, hb⟩ := mem_product.mp hwpool
    have ha' : w.1.natAbs ≤ W := (subset_offsets W {w.1}).mp (by simpa only [singleton_subset_iff]) w.1 (mem_singleton_self _)
    have hb' : w.2.natAbs ≤ W := (subset_offsets W {w.2}).mp (by simpa only [singleton_subset_iff]) w.2 (mem_singleton_self _)
    exact hNf N (by omega) H W Q w.1 w.2 hH hWN hQ ha' hb' hab (F w) (by
      intro n hnF
      obtain ⟨hnS, hp⟩ := mem_filter.mp hnF
      exact ⟨(hS n hnS).1, (hS n hnS).2.1, hp⟩)
  have hoff : ((offsets W).card : ℝ) ≤ (N : ℝ) ^ (ε / 4) := by
    rw [offsets_card]
    push_cast
    have hwone : (1 : ℝ) ≤ W := by exact_mod_cast hW
    exact (show (2 * W + 1 : ℝ) ≤ 3 * E * (Real.log N) ^ A₀ by nlinarith only [hwidth, hwone]).trans
      (hNo N (by omega))
  have hI : (I.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    have hfilter : I.card ≤ ((offsets W) ×ˢ (offsets W)).card := card_filter_le _ _
    calc
      _ ≤ ((offsets W).card : ℝ) * ((offsets W).card : ℝ) := by
        simpa only [card_product, Nat.cast_mul] using (show (I.card : ℝ) ≤ (((offsets W) ×ˢ (offsets W)).card : ℝ) by exact_mod_cast hfilter)
      _ ≤ (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 4) :=
        mul_le_mul hoff hoff (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  calc
    _ ≤ (I.card : ℝ) * (Q * (N : ℝ) ^ (ε / 2)) :=
      PaperP1.FiniteCoverCount.cardinal_le S I F _ hcover hF
    _ ≤ (N : ℝ) ^ (ε / 2) * (Q * (N : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right hI (mul_nonneg hQ (Real.rpow_nonneg hn.le _))
    _ = Q * (N : ℝ) ^ ε := by
      calc
        _ = Q * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hn, add_halves]

theorem comparable_count (C : ℕ) (hC : 1 ≤ C) (D E A₀ ε : ℝ)
    (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H W : ℕ, ∀ Q : ℝ,
      (H : ℝ) ≤ D * Real.log N → 0 < W → (W : ℝ) ≤ E * (Real.log N) ^ A₀ → 0 ≤ Q →
      ∀ S : Finset ℕ, (∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N ∧ HasPair H W n Q) →
      (S.card : ℝ) ≤ Q * (N : ℝ) ^ ε := by
  let η := ε / 2
  let T := distortion C
  have hη : 0 < η := by dsimp [η]; positivity
  have hT : 1 ≤ T := distortion_ge_one C
  obtain ⟨M₀, hM₀⟩ := dyadic_count (2 * D) (widthConstant E A₀) A₀ η (by positivity) hη
  obtain ⟨Np, hNp⟩ := PaperP1.ComparableSplitProductCount.prefactor_budget (indices C).card T η η hη
  refine ⟨max 3 (max (2 * C) (max (T ^ 2) (max (T * max 2 M₀) Np))), ?_⟩
  intro N hN H W Q hH hW hwidth hQ S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNcover : 2 * C ≤ N := by omega
  have hcells : ∀ j ∈ indices C,
      ((S.filter fun n ↦ base C N j ≤ n ∧ n ≤ 2 * base C N j).card : ℝ) ≤
        (base C N j : ℝ) ^ η * Q := by
    intro j hj
    let M := base C N j
    have hcomp := base_comparison C N j hC hNcover hj
    have hMlarge : max 2 M₀ ≤ M := base_large C N j (max 2 M₀) hC hNcover hj (by
      change T * max 2 M₀ ≤ N
      omega)
    have hlog := log_comparison T N M hT (by omega) (by omega) hcomp.1 hcomp.2
    have hHM : (H : ℝ) ≤ (2 * D) * Real.log M := by
      have hm := mul_le_mul_of_nonneg_left hlog.1 hD
      nlinarith only [hH, hm]
    have hWM := width_transfer E A₀ T N M W hT (by omega) (by omega) hcomp.1 hcomp.2 hwidth
    have hcount := hM₀ M (by omega) H W Q hHM hW hWM hQ
      (S.filter fun n ↦ base C N j ≤ n ∧ n ≤ 2 * base C N j) (by
        intro n hnS
        obtain ⟨hnS, hbox⟩ := mem_filter.mp hnS
        exact ⟨hbox.1, hbox.2, (hS n hnS).2.2⟩)
    simpa only [mul_comm Q] using hcount
  have hcount := PaperP1.ComparableCoverPower.power_bound C N hC hNcover S η Q hη.le hQ
    (fun n hnS ↦ ⟨(hS n hnS).1, (hS n hnS).2.1⟩) hcells
  have hp := hNp N (by omega)
  calc
    _ ≤ (((indices C).card : ℝ) * (T : ℝ) ^ η) * ((N : ℝ) ^ η * Q) := by
      simpa only [mul_assoc] using hcount
    _ ≤ (N : ℝ) ^ η * ((N : ℝ) ^ η * Q) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg (Real.rpow_nonneg hn.le _) hQ)
    _ = Q * (N : ℝ) ^ ε := by
      calc
        _ = Q * ((N : ℝ) ^ η * (N : ℝ) ^ η) := by ring
        _ = Q * (N : ℝ) ^ (η + η) := by rw [← Real.rpow_add hn]
        _ = _ := by congr 2; dsimp [η]; ring

theorem real_bounds_count (a b D E A₀ ε : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H W : ℕ, ∀ Q : ℝ,
      (H : ℝ) ≤ D * Real.log N → 0 < W → (W : ℝ) ≤ E * (Real.log N) ^ A₀ → 0 ≤ Q →
      ∀ S : Finset ℕ, (∀ n ∈ S, a * N ≤ n ∧ (n : ℝ) ≤ b * N ∧ HasPair H W n Q) →
      (∀ n ∈ S, ∀ u : ℤ, u.natAbs ≤ W → 0 < (n : ℤ) + u ∧
        (PaperP1.LinearKernelFibres.value n u : ℤ) = (n : ℤ) + u) ∧
      (S.card : ℝ) ≤ Q * (N : ℝ) ^ ε := by
  obtain ⟨C, hC, hcompare⟩ := exists_nat_comparison a b ha
  obtain ⟨Nc, hNc⟩ := comparable_count C hC D E A₀ ε hD hε
  obtain ⟨Nv, hNv⟩ := PaperP1.ComparableSplitProductCount.width_lt_centre C E A₀
  refine ⟨max Nc Nv, ?_⟩
  intro N hN H W Q hH hW hwidth hQ S hS
  have hcomp : ∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N := by
    intro n hnS
    exact hcompare N n (hS n hnS).1 (hS n hnS).2.1
  constructor
  · intro n hnS u hu
    have hWn := hNv N (by omega) n W (hcomp n hnS).1 hwidth
    have hlow : -(W : ℤ) ≤ u := by
      have habs : |u| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hu
      exact (abs_le.mp habs).1
    have hnW : (W : ℤ) < n := by exact_mod_cast hWn
    have hp : 0 < (n : ℤ) + u := by omega
    refine ⟨hp, ?_⟩
    change (((n : ℤ) + u).natAbs : ℤ) = (n : ℤ) + u
    rw [← Int.abs_eq_natAbs, abs_of_pos hp]
  · exact hNc N (by omega) H W Q hH hW hwidth hQ S (by
      intro n hnS
      exact ⟨(hcomp n hnS).1, (hcomp n hnS).2, (hS n hnS).2.2⟩)

theorem companion_T6_1 (a b D E A₀ ε : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H W : ℕ, ∀ q : ℝ,
      (H : ℝ) ≤ D * Real.log N → 0 < W → (W : ℝ) ≤ E * (Real.log N) ^ A₀ →
      ∀ S : Finset ℕ, (∀ n ∈ S, a * N ≤ n ∧ (n : ℝ) ≤ b * N ∧ HasPair H W n ((N : ℝ) ^ q)) →
      (∀ n ∈ S, ∀ u : ℤ, u.natAbs ≤ W → 0 < (n : ℤ) + u ∧
        (PaperP1.LinearKernelFibres.value n u : ℤ) = (n : ℤ) + u) ∧
      (S.card : ℝ) ≤ (N : ℝ) ^ (q + ε) := by
  obtain ⟨N₀, hN₀⟩ := real_bounds_count a b D E A₀ ε ha hD hε
  refine ⟨max 1 N₀, ?_⟩
  intro N hN H W q hH hW hwidth S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc := hN₀ N (by omega) H W ((N : ℝ) ^ q) hH hW hwidth (Real.rpow_nonneg hn.le _) S hS
  exact ⟨hc.1, by simpa only [← Real.rpow_add hn] using hc.2⟩

theorem critical_block_count (a b D E C ε : ℝ) (ha : 0 < a)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H W : ℕ, ∀ q : ℝ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (H : ℝ) ≤ D * (L + 1 : ℕ) → 0 < W → (W : ℝ) ≤ E * (L + 1 : ℕ) →
      ∀ S : Finset ℕ, (∀ n ∈ S, a * N ≤ n ∧ (n : ℝ) ≤ b * N ∧ HasPair H W n ((N : ℝ) ^ q)) →
      (∀ n ∈ S, ∀ u : ℤ, u.natAbs ≤ W → 0 < (n : ℤ) + u ∧
        (PaperP1.LinearKernelFibres.value n u : ℤ) = (n : ℤ) + u) ∧
      (S.card : ℝ) ≤ (N : ℝ) ^ (q + ε) := by
  obtain ⟨Nb, hNb⟩ := PaperP1.CriticalBandScale.critical_band_scale C
  obtain ⟨Nc, hNc⟩ := companion_T6_1 a b (D * PaperP1.CriticalBandScale.upperScale)
    (E * PaperP1.CriticalBandScale.upperScale) 1 ε ha
    (mul_nonneg hD PaperP1.CriticalBandScale.upperScale_pos.le) hε
  refine ⟨max Nb Nc, ?_⟩
  intro N hN L H W q hband hH hW hwidth S hS
  have hB := (hNb N (by omega) L hband).2
  have hHlog : (H : ℝ) ≤ (D * PaperP1.CriticalBandScale.upperScale) * Real.log N :=
    hH.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hB hD)
  have hWlog : (W : ℝ) ≤ (E * PaperP1.CriticalBandScale.upperScale) * (Real.log N) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    exact hwidth.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hB hE)
  exact hNc N (by omega) H W q hHlog hW hWlog S hS

end PaperP1.TwoSmallKernelCount
