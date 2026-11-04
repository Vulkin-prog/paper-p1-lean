module

public import PaperP1.Asymptotics.TwoProgressionSublinear
public import PaperP1.Arithmetic.NormalizedPairGeometry

/-! # A base-sensitive residual-rank criterion for actual normalized pairs

No dyadic interval or critical-band premise enters this criterion. The
actual base x controls the logarithmic Runge distance; the height bound
and normalized two-progression geometry remain unchanged.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedPairResidualCriterion

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets
  PaperP1.NormalizedPairGeometry PaperP1.TwoProgressionPrimeRows PaperP1.FiniteResidualRank

theorem rank_sublinear_of_geometry (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ B₀ : ℕ, ∀ L a b x y : ℕ, max B₀ 2 ≤ L + 1 →
      0 < a → a ≤ b → b ≤ (L + 1) ^ 3 → 8 * (L + 1) ≤ x → 0 < y →
      2 * Real.log 2 ≤ Real.log x → c * (L + 1 : ℕ) ≤ Real.log x / 2 →
      ∀ i j : Fin (L + 1), b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j →
      (Module.finrank F₂ (valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤ ε * (L + 1) := by
  obtain ⟨Bcore, hcore⟩ := TwoProgressionSublinear.rank_sublinear c 11 1 2 ε 6 hc (by norm_num) hε
  refine ⟨Bcore, ?_⟩
  intro L a b x y hBcore ha hab hheight hBN hy hlogLarge hlogWidth i j hunit
  let B : ℕ := L + 1
  change max Bcore 2 ≤ B at hBcore
  change b ≤ B ^ 3 at hheight
  change 8 * B ≤ x at hBN
  have hBtwo : 2 ≤ B := (le_max_right _ _).trans hBcore
  have hb : 0 < b := ha.trans_le hab
  have hx : 0 < x := by omega
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  let A : ℕ := b * startCompleteVertexLabel x L i
  let U : ℕ := A - b * L
  let R : ℕ := 2 * b * L
  have hanchor := anchor_geometry hBN (le_refl x) hb i
  have hA : b * L ≤ A := hanchor.1
  have hU : 2 * R ≤ U := by dsimp [R, U, A]; nlinarith [hanchor.2.1]
  have hxU : x ≤ 2 * U := hanchor.2.2
  have hR : 1 ≤ R := by
    have hL : 0 < L := by dsimp [B] at hBtwo; omega
    have hpos : 0 < R := by dsimp [R]; positivity
    omega
  have hUlog : c * B ≤ Real.log U := by
    have hhalf : (x : ℝ) / 2 ≤ U := by
      have h : (x : ℝ) ≤ 2 * U := by exact_mod_cast hxU
      linarith
    have hmono := Real.log_le_log (by positivity : 0 < (x : ℝ) / 2) hhalf
    rw [Real.log_div hxpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hmono
    change c * B ≤ Real.log x / 2 at hlogWidth
    linarith only [hmono, hlogLarge, hlogWidth]
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

end PaperP1.NormalizedPairResidualCriterion
