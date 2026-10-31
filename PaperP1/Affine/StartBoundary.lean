/-
Adapted from Vulkin-prog/paper-c-lean, the one-start complete-boundary section
of PaperC/Affine/TwoStartSystem.lean, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0.
Changes: split from two-start material, public helper for direct axiom audit,
Lean 4.36 module declarations, namespaces and ring tactic name.
-/
module

public import PaperP1.Affine.StartSystem
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option maxHeartbeats 1200000

/-! # Complete vertex boundary of one run-start star -/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Model PaperP1.Arithmetic

namespace PaperP1.Affine

/-- Root vertex of a start star. -/
def startRootVertex (L : ℕ) : Fin (L + 1) :=
  ⟨0, by omega⟩

/-- The vertex at the non-root endpoint of row `i`. -/
def startTipVertex {L : ℕ} (i : Fin L) : Fin (L + 1) :=
  ⟨i.1 + 1, by omega⟩

/--
The other endpoint of row `i`: the root for row zero and the centre for
all remaining rows.
-/
def startBaseVertex {L : ℕ} (i : Fin L) : Fin (L + 1) :=
  if i.1 = 0 then
    startRootVertex L
  else
    ⟨1, Nat.succ_lt_succ (Nat.zero_lt_of_lt i.2)⟩

/-- Binary incidence column of one start row on all `L+1` vertices. -/
def startIncidenceColumn {L : ℕ} (i : Fin L) : Fin (L + 1) → F₂ :=
  Pi.single (startBaseVertex i) 1 +
    Pi.single (startTipVertex i) 1

/--
The complete vertex boundary of a start edge-coefficient vector.
-/
def startCompleteBoundary (L : ℕ) :
    (Fin L → F₂) →ₗ[F₂] (Fin (L + 1) → F₂) :=
  Fintype.linearCombination F₂ (startIncidenceColumn (L := L))

@[simp]
theorem startCompleteBoundary_apply
    {L : ℕ} (u : Fin L → F₂) (v : Fin (L + 1)) :
    startCompleteBoundary L u v =
      ∑ i : Fin L, u i * startIncidenceColumn i v := by
  simp [startCompleteBoundary,
    Fintype.linearCombination_apply, smul_eq_mul]

/--
A private complete-boundary vertex for row `i`: the root for row zero and
its leaf otherwise.
-/
def startPrivateVertex {L : ℕ} (i : Fin L) : Fin (L + 1) :=
  if i.1 = 0 then startRootVertex L else startTipVertex i

theorem startIncidenceColumn_apply_private
    {L : ℕ} (i j : Fin L) :
    startIncidenceColumn j (startPrivateVertex i) =
      if j = i then 1 else 0 := by
  classical
  by_cases hij : j = i
  · subst j
    by_cases hi0 : i.1 = 0
    · simp [startIncidenceColumn, startPrivateVertex,
        startBaseVertex, startRootVertex, startTipVertex,
        hi0]
    · have htip_ne_center :
          startTipVertex i ≠ (⟨1, by omega⟩ : Fin (L + 1)) := by
        intro h
        apply hi0
        have hv := congrArg Fin.val h
        simp [startTipVertex] at hv
        omega
      simp [startIncidenceColumn, startPrivateVertex,
        startBaseVertex, hi0,
        htip_ne_center]
  · by_cases hi0 : i.1 = 0
    · have hiRoot : startPrivateVertex i = startRootVertex L := by
        simp [startPrivateVertex, hi0]
      have hj0 : j.1 ≠ 0 := by
        intro hj0
        apply hij
        apply Fin.ext
        omega
      have hroot_ne_base :
          startRootVertex L ≠ startBaseVertex j := by
        simp [startRootVertex, startBaseVertex, hj0]
      have hroot_ne_tip :
          startRootVertex L ≠ startTipVertex j := by
        intro h
        have hv := congrArg Fin.val h
        simp [startRootVertex, startTipVertex] at hv
      simp [startIncidenceColumn, hiRoot,
        hroot_ne_base, hroot_ne_tip, hij]
    · have hj_tip_ne :
          startTipVertex j ≠ startTipVertex i := by
        intro h
        apply hij
        apply Fin.ext
        have hv := congrArg Fin.val h
        simp [startTipVertex] at hv
        omega
      by_cases hj0 : j.1 = 0
      · have htip_ne_root :
            startTipVertex i ≠ startRootVertex L := by
          intro h
          have hv := congrArg Fin.val h
          simp [startTipVertex, startRootVertex] at hv
        have htip_ne_center :
            startTipVertex i ≠ startTipVertex j := by
          exact Ne.symm hj_tip_ne
        simp [startIncidenceColumn, startPrivateVertex,
          startBaseVertex, hi0, hj0,
          htip_ne_root, htip_ne_center, hij]
      · have htip_ne_center :
            startTipVertex i ≠ (⟨1, by omega⟩ : Fin (L + 1)) := by
          intro h
          apply hi0
          have hv := congrArg Fin.val h
          simp [startTipVertex] at hv
          omega
        have htip_ne_tip :
            startTipVertex i ≠ startTipVertex j :=
          Ne.symm hj_tip_ne
        simp [startIncidenceColumn, startPrivateVertex,
          startBaseVertex, hi0, hj0,
          htip_ne_center, htip_ne_tip, hij]

/-- The complete boundary determines every start-row coefficient. -/
theorem startCompleteBoundary_injective
    (L : ℕ) :
    Function.Injective (startCompleteBoundary L) := by
  intro u v huv
  funext i
  have hi := congrFun huv (startPrivateVertex i)
  simp only [startCompleteBoundary_apply] at hi
  calc
    u i = ∑ j : Fin L, u j *
        startIncidenceColumn j (startPrivateVertex i) := by
      symm
      simp_rw [startIncidenceColumn_apply_private i]
      simp
    _ = ∑ j : Fin L, v j *
        startIncidenceColumn j (startPrivateVertex i) := hi
    _ = v i := by
      simp_rw [startIncidenceColumn_apply_private i]
      simp

/-- Integer label of a complete start vertex. -/
def startCompleteVertexLabel (x L : ℕ) (v : Fin (L + 1)) : ℕ :=
  if v.1 = 0 then x - 1 else x + (v.1 - 1)

/-- Parity-vector row corresponding to one edge of the start star. -/
def startEdgeParity (x p : ℕ) {L : ℕ} (i : Fin L) : F₂ :=
  if i.1 = 0 then
    parityVec (x - 1) p + parityVec x p
  else
    parityVec x p + parityVec (x + i.1) p

@[simp]
theorem startCompleteVertexLabel_root
    (x L : ℕ) :
    startCompleteVertexLabel x L (startRootVertex L) = x - 1 := by
  simp [startCompleteVertexLabel, startRootVertex]

@[simp]
theorem startCompleteVertexLabel_tip
    (x : ℕ) {L : ℕ} (i : Fin L) :
    startCompleteVertexLabel x L (startTipVertex i) = x + i.1 := by
  simp [startCompleteVertexLabel, startTipVertex]

theorem startCompleteVertexLabel_base
    (x : ℕ) {L : ℕ} (i : Fin L) :
    startCompleteVertexLabel x L (startBaseVertex i) =
      if i.1 = 0 then x - 1 else x := by
  by_cases hi : i.1 = 0
  · simp [startBaseVertex, hi]
  · simp [startBaseVertex, startCompleteVertexLabel, hi]

/-- A row parity vector is the sum of the parity vectors at its endpoints. -/
theorem startEdgeParity_eq_endpoint_sum
    (x p : ℕ) {L : ℕ} (i : Fin L) :
    startEdgeParity x p i =
      parityVec (startCompleteVertexLabel x L (startBaseVertex i)) p +
        parityVec (startCompleteVertexLabel x L (startTipVertex i)) p := by
  by_cases hi : i.1 = 0
  · simp [startEdgeParity, startCompleteVertexLabel_base, hi]
  · simp [startEdgeParity, startCompleteVertexLabel_base, hi]

/--
Incidence form of one parity row: sum the vertex parity coordinates against
the row's incidence column.
-/
theorem startEdgeParity_eq_sum_incidence
    (x p : ℕ) {L : ℕ} (i : Fin L) :
    startEdgeParity x p i =
      ∑ v : Fin (L + 1),
        startIncidenceColumn i v *
          parityVec (startCompleteVertexLabel x L v) p := by
  rw [startEdgeParity_eq_endpoint_sum]
  simp [startIncidenceColumn, Pi.single_apply,
    add_mul, Finset.sum_add_distrib]

/--
Line--boundary identity for a complete start star.

The linear combination of edge parity rows equals the linear combination of
vertex parity vectors selected by the complete boundary.
-/
theorem sum_startEdgeParity_eq_sum_completeBoundary
    (x p : ℕ) {L : ℕ} (u : Fin L → F₂) :
    (∑ i : Fin L, u i * startEdgeParity x p i) =
      ∑ v : Fin (L + 1),
        startCompleteBoundary L u v *
          parityVec (startCompleteVertexLabel x L v) p := by
  simp_rw [startEdgeParity_eq_sum_incidence]
  calc
    (∑ i : Fin L,
        u i *
          ∑ v : Fin (L + 1),
            startIncidenceColumn i v *
              parityVec (startCompleteVertexLabel x L v) p) =
        ∑ i : Fin L, ∑ v : Fin (L + 1),
          u i *
            (startIncidenceColumn i v *
              parityVec (startCompleteVertexLabel x L v) p) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
    _ = ∑ v : Fin (L + 1), ∑ i : Fin L,
          u i *
            (startIncidenceColumn i v *
              parityVec (startCompleteVertexLabel x L v) p) :=
      Finset.sum_comm
    _ = ∑ v : Fin (L + 1),
          (∑ i : Fin L, u i * startIncidenceColumn i v) *
            parityVec (startCompleteVertexLabel x L v) p := by
          apply Finset.sum_congr rfl
          intro v _hv
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          ring1
    _ = ∑ v : Fin (L + 1),
          startCompleteBoundary L u v *
            parityVec (startCompleteVertexLabel x L v) p := by
          simp only [startCompleteBoundary_apply]

end PaperP1.Affine
