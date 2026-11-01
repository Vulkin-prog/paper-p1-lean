module

public import PaperP1.Asymptotics.BlockSupportCount

/-! # Actual fixed offset and dilation choices preserve the stronger support bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BlockSupportParameters

open Finset PaperP1.BoundedIntegerMotifs

def ShapeCode (V d h D : ℕ) := (Fin d → offsets V) × (Fin h → Fin D)

instance (V d h D : ℕ) : Fintype (ShapeCode V d h D) := by unfold ShapeCode; infer_instance

def population {r V d h D : ℕ} (G : Finset ℕ)
    (blocks : ShapeCode V d h D → Fin r → ℕ → Finset ℕ) (s : ℕ) : Finset (Fin r → ℕ) := by
  classical
  exact univ.biUnion fun q ↦ PaperP1.BlockSupportProjection.population G (blocks q) s

def records {r V d h D : ℕ} (G : Finset ℕ)
    (blocks : ShapeCode V d h D → Fin r → ℕ → Finset ℕ) (s : ℕ) :
    Finset (Σ _q : ShapeCode V d h D, Fin r → ℕ) := by
  classical
  exact univ.sigma fun q ↦ PaperP1.BlockSupportProjection.population G (blocks q) s

theorem code_card (V d h D : ℕ) : Fintype.card (ShapeCode V d h D) = (2 * V + 1) ^ d * D ^ h := by
  simp only [ShapeCode, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, offsets_card]

theorem records_bound {r V d h D : ℕ} (G : Finset ℕ)
    (blocks : ShapeCode V d h D → Fin r → ℕ → Finset ℕ) (s : ℕ) (B : ℝ)
    (hB : ∀ q, ((PaperP1.BlockSupportProjection.population G (blocks q) s).card : ℝ) ≤ B) :
    ((records G blocks s).card : ℝ) ≤ (Fintype.card (ShapeCode V d h D) : ℝ) * B := by
  classical
  calc
    _ = ∑ q : ShapeCode V d h D, ((PaperP1.BlockSupportProjection.population G (blocks q) s).card : ℝ) := by
      rw [records, card_sigma, Nat.cast_sum]
    _ ≤ ∑ _q : ShapeCode V d h D, B := sum_le_sum (fun q _ ↦ hB q)
    _ = _ := by simp

theorem code_budget (d h D : ℕ) (F ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ V : ℕ, (V : ℝ) ≤ F * Real.log N →
      (Fintype.card (ShapeCode V d h D) : ℝ) ≤ (N : ℝ) ^ ε := by
  let K := (2 * F + 1) ^ d * (D : ℝ) ^ h
  obtain ⟨NP, hNP⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow K (d : ℝ) ε hε
  obtain ⟨NL, hNL⟩ := Filter.eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (Filter.eventually_ge_atTop 1))
  refine ⟨max NP NL, ?_⟩
  intro N hN V hV
  have hlog : 1 ≤ Real.log N := hNL N (by omega)
  have hbase : (2 * V + 1 : ℝ) ≤ (2 * F + 1) * Real.log N := by nlinarith only [hV, hlog]
  have hcard : (Fintype.card (ShapeCode V d h D) : ℝ) = (2 * V + 1 : ℝ) ^ d * (D : ℝ) ^ h := by
    exact_mod_cast code_card V d h D
  calc
    _ = (2 * V + 1 : ℝ) ^ d * (D : ℝ) ^ h := hcard
    _ ≤ ((2 * F + 1) * Real.log N) ^ d * (D : ℝ) ^ h :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase d) (pow_nonneg (Nat.cast_nonneg _) _)
    _ = K * (Real.log N) ^ d := by rw [mul_pow]; dsimp [K]; ring
    _ ≤ (N : ℝ) ^ ε := by simpa only [Real.rpow_natCast] using hNP N (by omega)

theorem uniform_count (r s C d h D : ℕ) (hs : 0 < s) (hC : 1 ≤ C) (a b E F ε : ℝ)
    (ha : 0 < a) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ V M : ℕ, ∀ G : Finset ℕ,
      ∀ blocks : ShapeCode V d h D → Fin r → ℕ → Finset ℕ,
      (V : ℝ) ≤ F * Real.log N → G ⊆ Ico M (M + C * N) →
      (∀ q i, ∀ x ∈ G, ∀ v ∈ blocks q i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ q i, ∀ x ∈ G, ∀ v ∈ blocks q i x, (((v : ℤ) - x).natAbs : ℝ) ≤ E * Real.log N) →
      ((population G blocks s).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + ε) ∧
      ((records G blocks s).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + ε) := by
  classical
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NI, hNI⟩ := PaperP1.BlockSupportCount.interval_count r s C hs hC a b E η ha hE hη
  obtain ⟨NQ, hNQ⟩ := code_budget d h D F η hη
  refine ⟨max 2 (max NI NQ), ?_⟩
  intro N hN V M G blocks hV hG hvalues hdist
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcover : ∀ n ∈ population G blocks s,
      ∃ q ∈ (univ : Finset (ShapeCode V d h D)), n ∈ PaperP1.BlockSupportProjection.population G (blocks q) s := by
    intro n hnP
    exact mem_biUnion.mp hnP
  have hclass : ∀ q ∈ (univ : Finset (ShapeCode V d h D)),
      ((PaperP1.BlockSupportProjection.population G (blocks q) s).card : ℝ) ≤
        (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + η) :=
    fun q _ ↦ hNI N (by omega) M G (blocks q) hG (hvalues q) (hdist q)
  have hc := PaperP1.FiniteCoverCount.cardinal_le (population G blocks s)
    (univ : Finset (ShapeCode V d h D)) (fun q ↦ PaperP1.BlockSupportProjection.population G (blocks q) s) _ hcover hclass
  have hcommon : (Fintype.card (ShapeCode V d h D) : ℝ) * (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + η) ≤
      (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + ε) := by
    calc
      _ ≤ (N : ℝ) ^ η * (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + η) :=
        mul_le_mul_of_nonneg_right (hNQ N (by omega) V hV) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; dsimp [η]; ring
  have hpop : ((population G blocks s).card : ℝ) ≤
      (Fintype.card (ShapeCode V d h D) : ℝ) * (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + η) := by
    simpa only [card_univ] using hc
  exact ⟨hpop.trans hcommon,
    (records_bound G blocks s _ (fun q ↦ hclass q (mem_univ q))).trans hcommon⟩

theorem critical_count (r s C d h D : ℕ) (hs : 0 < s) (hC : 1 ≤ C) (a b E F Cband ε : ℝ)
    (ha : 0 < a) (hE : 0 ≤ E) (hF : 0 ≤ F) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L V M : ℕ, ∀ G : Finset ℕ,
      ∀ blocks : ShapeCode V d h D → Fin r → ℕ → Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband → (V : ℝ) ≤ F * (L + 1 : ℕ) →
      G ⊆ Ico M (M + C * N) →
      (∀ q i, ∀ x ∈ G, ∀ v ∈ blocks q i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ q i, ∀ x ∈ G, ∀ v ∈ blocks q i x, (((v : ℤ) - x).natAbs : ℝ) ≤ E * (L + 1 : ℕ)) →
      ((population G blocks s).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + ε) ∧
      ((records G blocks s).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + ε) := by
  obtain ⟨NI, hNI⟩ := uniform_count r s C d h D hs hC a b
    (E * PaperP1.CriticalBandScale.upperScale) (F * PaperP1.CriticalBandScale.upperScale) ε ha
    (mul_nonneg hE PaperP1.CriticalBandScale.upperScale_pos.le) hε
  obtain ⟨NB, hNB⟩ := PaperP1.CriticalBandScale.critical_band_scale Cband
  refine ⟨max NI NB, ?_⟩
  intro N hN L V M G blocks hband hV hG hvalues hdist
  have hW := (hNB N (by omega) L hband).2
  have hVlog : (V : ℝ) ≤ (F * PaperP1.CriticalBandScale.upperScale) * Real.log N := hV.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hW hF)
  have hElog : E * (L + 1 : ℕ) ≤ (E * PaperP1.CriticalBandScale.upperScale) * Real.log N := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hW hE
  exact hNI N (by omega) V M G blocks hVlog hG hvalues (fun q i x hx v hv ↦ (hdist q i x hx v hv).trans hElog)

theorem companion_T1_14 (r s C d h D : ℕ) (hs : 2 ≤ s) (hC : 1 ≤ C) (a b E F Cband ε : ℝ)
    (ha : 0 < a) (hE : 0 ≤ E) (hF : 0 ≤ F) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L V M : ℕ, ∀ G : Finset ℕ,
      ∀ blocks : ShapeCode V d h D → Fin r → ℕ → Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband → (V : ℝ) ≤ F * (L + 1 : ℕ) →
      G ⊆ Ico M (M + C * N) →
      (∀ q i, ∀ x ∈ G, ∀ v ∈ blocks q i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ q i, ∀ x ∈ G, ∀ v ∈ blocks q i x, (((v : ℤ) - x).natAbs : ℝ) ≤ E * (L + 1 : ℕ)) →
      ((population G blocks s).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) - 2 * s / (2 * s + 1) + ε) ∧
      ((records G blocks s).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) - 2 * s / (2 * s + 1) + ε) := by
  obtain ⟨N₀, hN₀⟩ := critical_count r s C d h D (by omega) hC a b E F Cband ε ha hE hF hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN L V M G blocks hband hV hG hvalues hdist
  have hc := hN₀ N (by omega) L V M G blocks hband hV hG hvalues hdist
  have hpower : (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + ε) ≤
      (N : ℝ) ^ ((r : ℝ) - 2 * s / (2 * s + 1) + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
      (by have h := PaperP1.BlockSupportCount.source_exponent r s hs; linarith only [h])
  exact ⟨hc.1.trans hpower, hc.2.trans hpower⟩

end PaperP1.BlockSupportParameters
