module

public import PaperP1.Coding.WindowRelationCode
public import PaperP1.Affine.StartCharacterSpace
public import PaperP1.Model.InfiniteStartFourier

/-!
# Local relation rank and exact run marginals

The consecutive-window relation code is identified with the kernel of the
actual even-square-class map. A finite Griesmer prime-count obstruction then
gives the two possible effective ranks and exact heterogeneous marginals.
No prime number theorem or asymptotic rigidity statement is assumed here.
-/

@[expose] public noncomputable section

namespace PaperP1.LocalRunRank

open PaperP1.Arithmetic PaperP1.Affine WindowRelationCode LocalRigidityCode
open LocalDefectBound Model.InfiniteStarts

local instance localRunRankPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem mem_start_windowRelationCode {x L : ℕ} (hx : 0 < x)
    (w : Fin (L + 1) → F₂) :
    w ∈ windowRelationCode (x - 1) (L + 1) ↔
      w ∈ LinearMap.ker (vertexParityMap x L) ∧
        w ∈ LinearMap.ker (startVertexSum L) := by
  rw [mem_windowRelationCode]
  simp only [LinearMap.mem_ker, vertexParityMap_apply, startVertexSum_apply,
    startCompleteVertexLabel_eq_offset hx]

/-- These are the same local even square relations, with or without the
even-selection subtype in their domain. -/
def relationEvenEquiv {x L : ℕ} (hx : 0 < x) :
    windowRelationCode (x - 1) (L + 1) ≃ₗ[F₂]
      LinearMap.ker (evenSquareClassMap x L) where
  toFun w := ⟨⟨w.val, ((mem_start_windowRelationCode hx _).mp w.property).2⟩,
    by
      change vertexParityMap x L w.val = 0
      exact ((mem_start_windowRelationCode hx _).mp w.property).1⟩
  invFun w := ⟨w.val.val, (mem_start_windowRelationCode hx _).mpr
    ⟨by
      change vertexParityMap x L w.val.val = 0
      exact w.property, w.val.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The missing effective dimensions are exactly the even square relations. -/
theorem squareClass_rank_add_relation_rank {x L : ℕ} (hx : 0 < x) :
    Module.finrank F₂ (squareClassSpace x L) +
      Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) = L := by
  have h := (evenSquareClassMap x L).finrank_range_add_finrank_ker
  have heven : Module.finrank F₂ (LinearMap.ker (startVertexSum L)) = L := by
    simpa only [Module.finrank_fin_fun] using (startBoundaryEquivEven L).finrank_eq.symm
  rw [heven, ← (relationEvenEquiv hx).finrank_eq] at h
  exact h

theorem squareClass_rank_le (x L : ℕ) (hx : 0 < x) :
    Module.finrank F₂ (squareClassSpace x L) ≤ L := by
  have h := squareClass_rank_add_relation_rank (L := L) hx
  omega

/-- A completely finite sufficient condition for the critical-band ranks. -/
theorem squareClass_rank_eq_or_pred {x L : ℕ} (hx : 0 < x)
    (hU : 2 * (L + 1) ≤ x - 1)
    (hobstruction : primeCount (L + 1) + 1 <
      GriesmerBound.griesmerSum 2 (rungeDistance (x - 1) (L + 1)) - 2) :
    Module.finrank F₂ (squareClassSpace x L) = L ∨
      Module.finrank F₂ (squareClassSpace x L) = L - 1 := by
  have hr := window_relation_finrank_lt (by omega : 1 ≤ L + 1) hU hobstruction
  have hid := squareClass_rank_add_relation_rank (L := L) hx
  omega

/-- Actual infinite-model marginal of a positive-probability start. -/
theorem infiniteMarginal_eq_squareClass_rank {x L : ℕ} (hL : 0 < L)
    (hp : 0 < infiniteMarginal x L) :
    infiniteMarginal x L = (2 ^ Module.finrank F₂ (squareClassSpace x L) : ℝ)⁻¹ := by
  let M := x + L
  have hcut : x + L ≤ M := le_rfl
  have hc := (infiniteMarginal_pos_iff_compatible hL hcut).mp hp
  rw [infiniteMarginal_eq_finite hcut]
  exact exactMarginal_start_eq_squareClass_rank hL hcut hc

/-- Both possible exact marginals under the finite critical-rank criterion.
Incompatible windows are excluded only by their actual zero probability. -/
theorem infiniteMarginal_eq_nominal_or_double {x L : ℕ} (hx : 0 < x) (hL : 0 < L)
    (hp : 0 < infiniteMarginal x L) (hU : 2 * (L + 1) ≤ x - 1)
    (hobstruction : primeCount (L + 1) + 1 <
      GriesmerBound.griesmerSum 2 (rungeDistance (x - 1) (L + 1)) - 2) :
    infiniteMarginal x L = (2 ^ L : ℝ)⁻¹ ∨
      infiniteMarginal x L = 2 * (2 ^ L : ℝ)⁻¹ := by
  rw [infiniteMarginal_eq_squareClass_rank hL hp]
  rcases squareClass_rank_eq_or_pred hx hU hobstruction with hr | hr
  · exact Or.inl (congrArg (fun d : ℕ ↦ (2 ^ d : ℝ)⁻¹) hr)
  · right
    rw [hr, show L = (L - 1) + 1 by omega, pow_succ]
    field_simp
    simp only [Nat.add_sub_cancel]

end PaperP1.LocalRunRank
