module

public import PaperP1.Arithmetic.BlockSupportProjection
public import PaperP1.Asymptotics.ValueHeightHalfCount

/-! # A half power for every nonzero projection in an arbitrary support

The complementary centres are counted freely. The complete conditional
half-count is instantiated uniformly at every actual fixed complement.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BlockSupportCount

open Finset PaperP1.EffectiveExposure

theorem uniform_count (r s C : ℕ) (hs : 0 < s) (hC : 1 ≤ C) (a b E ε : ℝ)
    (ha : 0 < a) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G : Finset ℕ, ∀ blocks : Fin r → ℕ → Finset ℕ,
      G.card ≤ C * N →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, (((v : ℤ) - x).natAbs : ℝ) ≤ E * Real.log N) →
      ((PaperP1.BlockSupportProjection.population G blocks s).card : ℝ) ≤
        (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + ε) := by
  classical
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have he := fun k : Fin r ↦ PaperP1.ValueHeightHalfCount.uniform_logarithmic_count
    (r - k.val) k.val a b E η ha hE hη
  choose NE hNE using he
  let p := (r : ℝ) - (s : ℝ) / 2
  let K := (Fintype.card (Code r) : ℝ) * (C : ℝ) ^ r
  obtain ⟨NF, hNF⟩ := PaperP1.HalfCountSchedule.factor_absorption K (p + η) η hη
  refine ⟨2 + NF + univ.sup NE, ?_⟩
  intro N hN G blocks hGcard hvalues hdist
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hEn : ∀ k : Fin r, NE k ≤ N := by
    intro k
    have hk : NE k ≤ univ.sup NE := le_sup (f := NE) (mem_univ k)
    omega
  have hcell : ∀ c ∈ PaperP1.BlockSupportProjection.codes r s,
      ((PaperP1.BlockSupportProjection.cell G blocks c).card : ℝ) ≤ (C : ℝ) ^ r * (N : ℝ) ^ (p + η) := by
    intro c hc
    have hB : ∀ old ∈ Fintype.piFinset (fun _ : Fin c.1.val ↦ G),
        ((PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) (oldValues c blocks old)).card : ℝ) ≤
          (N : ℝ) ^ (((r - c.1.val : ℕ) : ℝ) / 2 + η) := by
      intro old hold
      have holdG := Fintype.mem_piFinset.mp hold
      exact hNE c.1 N (hEn c.1) old G (rightBlocks c blocks) (fun i ↦ leftBlocks c blocks i (old i))
        (fun i x hx v hv ↦ hvalues _ x hx v hv)
        (fun i v hv ↦ hvalues _ (old i) (holdG i) v hv)
        (fun i x hx v hv ↦ hdist _ x hx v hv)
        (fun i v hv ↦ hdist _ (old i) (holdG i) v hv)
    have hfree : ((Fintype.piFinset (fun _ : Fin c.1.val ↦ G)).card : ℝ) ≤
        (C : ℝ) ^ r * (N : ℝ) ^ c.1.val := by
      rw [Fintype.card_piFinset_const, Nat.cast_pow]
      calc
        _ ≤ ((C : ℝ) * N) ^ c.1.val := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hGcard) _
        _ = (C : ℝ) ^ c.1.val * (N : ℝ) ^ c.1.val := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1 c.1.isLt.le) (pow_nonneg hn.le _)
    have hsize : s ≤ r - c.1.val := (mem_filter.mp hc).2
    have hsizeR : (s : ℝ) ≤ (r - c.1.val : ℕ) := by exact_mod_cast hsize
    have hsumR : (c.1.val : ℝ) + ((r - c.1.val : ℕ) : ℝ) = r := by
      exact_mod_cast Nat.add_sub_of_le c.1.isLt.le
    have hcost : (c.1.val : ℝ) + (((r - c.1.val : ℕ) : ℝ) / 2 + η) ≤ p + η := by
      dsimp [p]
      nlinarith only [hsizeR, hsumR]
    have hmul : (N : ℝ) ^ c.1.val * (N : ℝ) ^ (((r - c.1.val : ℕ) : ℝ) / 2 + η) =
        (N : ℝ) ^ ((c.1.val : ℝ) + (((r - c.1.val : ℕ) : ℝ) / 2 + η)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hn]
    have hraw := PaperP1.BlockSupportProjection.cell_count G blocks c _ hB
    calc
      _ ≤ ((C : ℝ) ^ r * (N : ℝ) ^ c.1.val) * (N : ℝ) ^ (((r - c.1.val : ℕ) : ℝ) / 2 + η) :=
        hraw.trans (mul_le_mul_of_nonneg_right hfree (Real.rpow_nonneg hn.le _))
      _ = (C : ℝ) ^ r * ((N : ℝ) ^ c.1.val * (N : ℝ) ^ (((r - c.1.val : ℕ) : ℝ) / 2 + η)) := mul_assoc _ _ _
      _ = (C : ℝ) ^ r * (N : ℝ) ^ ((c.1.val : ℝ) + (((r - c.1.val : ℕ) : ℝ) / 2 + η)) := congrArg _ hmul
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hcost) (pow_nonneg (Nat.cast_nonneg _) _)
  have hcover := PaperP1.FiniteCoverCount.cardinal_le (PaperP1.BlockSupportProjection.population G blocks s)
    (PaperP1.BlockSupportProjection.codes r s) (PaperP1.BlockSupportProjection.cell G blocks)
    ((C : ℝ) ^ r * (N : ℝ) ^ (p + η)) (PaperP1.BlockSupportProjection.population_cover G blocks s hs) hcell
  have hcodes : ((PaperP1.BlockSupportProjection.codes r s).card : ℝ) ≤ Fintype.card (Code r) := by
    exact_mod_cast (card_le_univ (s := PaperP1.BlockSupportProjection.codes r s))
  calc
    _ ≤ (Fintype.card (Code r) : ℝ) * ((C : ℝ) ^ r * (N : ℝ) ^ (p + η)) :=
      hcover.trans (mul_le_mul_of_nonneg_right hcodes (by positivity))
    _ = K * (N : ℝ) ^ (p + η) := by dsimp [K]; ring
    _ ≤ (N : ℝ) ^ ((p + η) + η) := hNF N (by omega)
    _ = _ := by congr 1; dsimp [p, η]; ring

theorem source_exponent (r s : ℕ) (hs : 2 ≤ s) :
    (r : ℝ) - (s : ℝ) / 2 ≤ (r : ℝ) - 2 * s / (2 * s + 1) := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hden : (0 : ℝ) < 2 * s + 1 := by positivity
  have hfrac : 2 * (s : ℝ) / (2 * s + 1) ≤ (s : ℝ) / 2 :=
    (div_le_iff₀ hden).mpr (by nlinarith only [hsR])
  linarith only [hfrac]

theorem interval_count (r s C : ℕ) (hs : 0 < s) (hC : 1 ≤ C) (a b E ε : ℝ)
    (ha : 0 < a) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, ∀ G : Finset ℕ, ∀ blocks : Fin r → ℕ → Finset ℕ,
      G ⊆ Ico M (M + C * N) →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, (((v : ℤ) - x).natAbs : ℝ) ≤ E * Real.log N) →
      ((PaperP1.BlockSupportProjection.population G blocks s).card : ℝ) ≤
        (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + ε) := by
  obtain ⟨N₀, hN₀⟩ := uniform_count r s C hs hC a b E ε ha hE hε
  refine ⟨N₀, ?_⟩
  intro N hN M G blocks hG hvalues hdist
  have hcard : G.card ≤ C * N := (card_le_card hG).trans_eq (by simp)
  exact hN₀ N hN G blocks hcard hvalues hdist

theorem critical_interval_count (r s C : ℕ) (hs : 0 < s) (hC : 1 ≤ C) (a b D Cband ε : ℝ)
    (ha : 0 < a) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L M : ℕ, ∀ G : Finset ℕ, ∀ blocks : Fin r → ℕ → Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband → G ⊆ Ico M (M + C * N) →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, (((v : ℤ) - x).natAbs : ℝ) ≤ D * (L + 1 : ℕ)) →
      ((PaperP1.BlockSupportProjection.population G blocks s).card : ℝ) ≤
        (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + ε) := by
  obtain ⟨NI, hNI⟩ := interval_count r s C hs hC a b (D * PaperP1.CriticalBandScale.upperScale) ε
    ha (mul_nonneg hD PaperP1.CriticalBandScale.upperScale_pos.le) hε
  obtain ⟨NB, hNB⟩ := PaperP1.CriticalBandScale.critical_band_scale Cband
  refine ⟨max NI NB, ?_⟩
  intro N hN L M G blocks hband hG hvalues hdist
  have hwidth : D * (L + 1 : ℕ) ≤ (D * PaperP1.CriticalBandScale.upperScale) * Real.log N := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hNB N (by omega) L hband).2 hD
  exact hNI N (by omega) M G blocks hG hvalues (fun i x hx v hv ↦ (hdist i x hx v hv).trans hwidth)

theorem companion_T1_14 (r s C : ℕ) (hs : 2 ≤ s) (hC : 1 ≤ C) (a b D Cband ε : ℝ)
    (ha : 0 < a) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L M : ℕ, ∀ G : Finset ℕ, ∀ blocks : Fin r → ℕ → Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband → G ⊆ Ico M (M + C * N) →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, (((v : ℤ) - x).natAbs : ℝ) ≤ D * (L + 1 : ℕ)) →
      ((PaperP1.BlockSupportProjection.population G blocks s).card : ℝ) ≤
        (N : ℝ) ^ ((r : ℝ) - 2 * s / (2 * s + 1) + ε) := by
  obtain ⟨N₀, hN₀⟩ := critical_interval_count r s C (by omega) hC a b D Cband ε ha hD hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN L M G blocks hband hG hvalues hdist
  exact (hN₀ N (by omega) L M G blocks hband hG hvalues hdist).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
      (by have h := source_exponent r s hs; linarith only [h]))

end PaperP1.BlockSupportCount
