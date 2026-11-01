module

public import PaperP1.Asymptotics.TwoProgressionSublinear
public import PaperP1.Arithmetic.NormalizedPairGeometry

/-! # Uniform residual rank on the actual normalized aligned pair of height B^3 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedPairResidual

open Finset Filter PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets
  PaperP1.NormalizedPairGeometry PaperP1.TwoProgressionPrimeRows PaperP1.FiniteResidualRank
  PaperP1.CriticalBandScale

set_option maxHeartbeats 800000 in
theorem rank_sublinear (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ (L + 1) ^ 3 → N ≤ x → 0 < y →
      ∀ i j : Fin (L + 1), b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j →
      (Module.finrank F₂ (valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤ ε * (L + 1) := by
  let c : ℝ := 1 / (2 * upperScale)
  have hc : 0 < c := by dsimp [c]; exact div_pos zero_lt_one (mul_pos (by norm_num) upperScale_pos)
  obtain ⟨Bcore, hcore⟩ := TwoProgressionSublinear.rank_sublinear c 11 1 2 ε 6 hc (by norm_num) hε
  obtain ⟨Nband, hband⟩ := critical_band_scale C
  obtain ⟨Nlog, hlog⟩ := ElementaryLogGrowth.log_ge_eventually
    (max (2 * Real.log 2) ((max Bcore 2 : ℕ) / lowerScale))
  have hthin : ∀ᶠ N : ℕ in atTop, Real.log N / N < 1 / (8 * upperScale) :=
    (tendsto_order.1 PrimeLogBudget.log_nat_div_self_tendsto).2 _
      (div_pos zero_lt_one (mul_pos (by norm_num) upperScale_pos))
  obtain ⟨Nthin, hNthin⟩ := eventually_atTop.1 hthin
  refine ⟨max Nband (max Nlog (max Nthin 8)), ?_⟩
  intro N hN L a b x y hcrit ha hab hheight hxN hy i j hunit
  let B : ℕ := L + 1
  change b ≤ B ^ 3 at hheight
  have hNband : Nband ≤ N := (le_max_left _ _).trans hN
  have hNlog : Nlog ≤ N := (le_max_left Nlog _).trans ((le_max_right _ _).trans hN)
  have hNth : Nthin ≤ N := (le_max_left Nthin 8).trans ((le_max_right Nlog _).trans ((le_max_right _ _).trans hN))
  have hNeight : 8 ≤ N := (le_max_right Nthin 8).trans ((le_max_right Nlog _).trans ((le_max_right _ _).trans hN))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hBlo, hBhi⟩ := hband N hNband L hcrit
  have hloglarge := (hlog N hNlog).1
  have hBcore : max Bcore 2 ≤ B := by
    have h := (div_le_iff₀ lowerScale_pos).mp ((le_max_right _ _).trans hloglarge)
    have hBreal : ((max Bcore 2 : ℕ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by nlinarith
    exact_mod_cast hBreal
  have hBtwo : 2 ≤ B := (le_max_right _ _).trans hBcore
  have hBN : 8 * B ≤ N := by
    have h := (div_lt_div_iff₀ hNpos (mul_pos (by norm_num) upperScale_pos)).mp (hNthin N hNth)
    have hBNreal : (8 * B : ℕ) ≤ (N : ℝ) := by
      push_cast
      nlinarith only [h, hBhi]
    exact_mod_cast hBNreal
  have hb : 0 < b := ha.trans_le hab
  have hx : 0 < x := by omega
  let A : ℕ := b * startCompleteVertexLabel x L i
  let U : ℕ := A - b * L
  let R : ℕ := 2 * b * L
  have hanchor := anchor_geometry hBN hxN hb i
  have hA : b * L ≤ A := hanchor.1
  have hU : 2 * R ≤ U := by dsimp [R, U, A]; nlinarith [hanchor.2.1]
  have hNU : N ≤ 2 * U := hanchor.2.2
  have hR : 1 ≤ R := by
    have hL : 0 < L := by dsimp [B] at hBtwo; omega
    have hpos : 0 < R := by dsimp [R]; positivity
    omega
  have hUpos : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
  have hUlog : c * B ≤ Real.log U := by
    have hhalf : (N : ℝ) / 2 ≤ U := by
      have h : (N : ℝ) ≤ 2 * U := by exact_mod_cast hNU
      linarith
    have hmono := Real.log_le_log (by positivity : 0 < (N : ℝ) / 2) hhalf
    rw [Real.log_div hNpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hmono
    have hcB : c * B ≤ Real.log N / 2 := by
      calc
        _ = (B : ℝ) / (2 * upperScale) := by dsimp [c]; ring
        _ ≤ Real.log N / 2 := (div_le_iff₀ (mul_pos (by norm_num) upperScale_pos)).mpr (by nlinarith)
    have hlogN : 2 * Real.log 2 ≤ Real.log N := (le_max_left _ _).trans hloglarge
    linarith
  have hRwidth : R ≤ 2 * B ^ 4 := by
    have hprod := Nat.mul_le_mul hheight (show L ≤ B by omega)
    have hpowers : B ^ 3 * B = B ^ 4 := by ring
    dsimp [R]
    nlinarith only [hprod, hpowers]
  have hRlog := logarithmic_width hBtwo (by omega : 0 < R) hRwidth
  have habheight : b * a ≤ B ^ 6 := by
    have hprod := Nat.mul_le_mul hheight (hab.trans hheight)
    have hpowers : B ^ 3 * B ^ 3 = B ^ 6 := by ring
    nlinarith only [hprod, hpowers]
  suffices hresult : (Module.finrank F₂ (valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤ ε * (B : ℝ) by
    simpa only [B, Nat.cast_add, Nat.cast_one] using hresult
  apply hcore B ((le_max_left _ _).trans hBcore) (NormalizedWindowSets.union a b x y L)
    B b a (x - 1) (y - 1) L L U R
  · exact le_rfl
  · simp only [one_mul, le_refl]
  · exact hb
  · exact ha
  · exact habheight
  · omega
  · omega
  · rw [NormalizedWindowSets.union, normalized_progression hx, normalized_progression hy]
  · intro n hn
    exact (union_bounds hab hx hy i j hunit n hn).1
  · intro n hn
    have hbound := (union_bounds hab hx hy i j hunit n hn).2
    have heq : A + b * L = U + R := by
      have hcancel := Nat.sub_add_cancel hA
      dsimp [U, R]
      nlinarith only [hcancel]
    change n ≤ U + R
    rw [← heq]
    exact hbound
  · exact hR
  · exact hU
  · exact hUlog
  · exact hRlog
  · exact_mod_cast union_card_le ha hb hx hy

end PaperP1.NormalizedPairResidual
