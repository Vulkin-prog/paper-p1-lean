module

public import PaperP1.Arithmetic.OffsetRootExceptionalSet
public import PaperP1.Combinatorics.DiscardTouchedSupports
public import PaperP1.Algebra.SplitRootPolynomial

/-! # Companion T20.5: common roots and removal of at most two equations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetRootPolynomials

open Finset Polynomial PaperP1.Arithmetic PaperP1.OffsetRootSeparation
open PaperP1.OffsetRootExceptionalSet PaperP1.TwoPointSquareClasses

def leading {L : ℕ} (α : ℚ) : Coordinate L → ℚ := Sum.elim (fun _ ↦ 1) (fun _ ↦ α)

def linearFactor {L : ℕ} (α β : ℚ) : Coordinate L → ℚ[X] :=
  Sum.elim (fun u ↦ X + C (offset u)) (fun v ↦ C α * X + C (β + offset v))

def polynomial {L : ℕ} (α β : ℚ) (S : Finset (Coordinate L)) : ℚ[X] :=
  ∏ v ∈ S, linearFactor α β v

theorem leading_ne_zero {L : ℕ} (α : ℚ) (hα : α ≠ 0) (v : Coordinate L) : leading α v ≠ 0 := by
  cases v <;> simp [leading, hα]

theorem linearFactor_eq_split {L : ℕ} (α β : ℚ) (hα : α ≠ 0) (v : Coordinate L) :
    linearFactor α β v = PaperP1.SplitRootPolynomial.factor (root α β) (leading α) v := by
  cases v with
  | inl u => simp [linearFactor, root, leading, PaperP1.SplitRootPolynomial.factor, leftRoot]
  | inr v =>
    change C α * X + C (β + offset v) = C α * (X - C (rightRoot α β v))
    have hq : α * rightRoot α β v = -(β + offset v) := by unfold rightRoot; field_simp
    rw [mul_sub, ← C_mul, hq, C_neg, sub_neg_eq_add]

theorem polynomial_eq_split {L : ℕ} (α β : ℚ) (hα : α ≠ 0) (S : Finset (Coordinate L)) :
    polynomial α β S = PaperP1.SplitRootPolynomial.polynomial (root α β) (leading α) S := by
  apply prod_congr rfl
  intro v _
  exact linearFactor_eq_split α β hα v

theorem polynomial_squarefree {L : ℕ} (α β : ℚ) (hα : α ≠ 0) (S : Finset (Coordinate L))
    (hinj : Set.InjOn (root α β) (S : Set (Coordinate L))) : Squarefree (polynomial α β S) := by
  rw [polynomial_eq_split α β hα]
  exact PaperP1.SplitRootPolynomial.polynomial_squarefree _ _ S
    (fun v _ ↦ leading_ne_zero α hα v) hinj

theorem isRoot_iff {L : ℕ} (α β : ℚ) (hα : α ≠ 0) (S : Finset (Coordinate L)) (t : ℚ) :
    Polynomial.IsRoot (polynomial α β S) t ↔ ∃ v ∈ S, root α β v = t := by
  rw [polynomial_eq_split α β hα]
  exact PaperP1.SplitRootPolynomial.isRoot_iff _ _ S (fun v _ ↦ leading_ne_zero α hα v) t

def Conclusion {ι : Type*} [DecidableEq ι] (L : ℕ) (α β : ℚ)
    (I : Finset ι) (S : ι → Finset (Coordinate L)) : Prop :=
  (commonRoots L α β).card ≤ 1 ∧ ∃ D : Finset ι, D ⊆ I ∧ D.card ≤ 2 ∧
    (∀ i ∈ I \ D, Squarefree (polynomial α β (S i))) ∧
    (∀ i ∈ I \ D, ∀ j ∈ I \ D, i ≠ j → ∀ t : ℚ,
      Polynomial.IsRoot (polynomial α β (S i)) t → ¬Polynomial.IsRoot (polynomial α β (S j)) t)

theorem root_separation {ι : Type*} [DecidableEq ι]
    (x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hinj : Function.Injective (evenSquareClassMap x L))
    (hdirect : Disjoint (squareClassSpace x L) (squareClassSpace y L))
    (α β : ℚ) (hα : α ≠ 0) (hline : (y : ℚ) = α * (x : ℚ) + β)
    (I : Finset ι) (S : ι → Finset (Coordinate L)) (hdisj : (↑I : Set ι).PairwiseDisjoint S) :
    Conclusion L α β I S := by
  obtain ⟨H, hHcard, hroot⟩ := exists_exceptional_coordinates x y L hx hy hinj hdirect α β hα hline
  obtain ⟨D, hDI, hDcard, havoid⟩ := PaperP1.DiscardTouchedSupports.exists_discard I S H hdisj
  refine ⟨commonRoots_card_le_one x y L hx hy hinj hdirect α β hα hline,
    D, hDI, hDcard.trans hHcard, ?_, ?_⟩
  · intro i hi
    apply polynomial_squarefree α β hα (S i)
    intro u hu v hv heq
    exact hroot (havoid i hi u hu) (havoid i hi v hv) heq
  · intro i hi j hj hij t hti htj
    obtain ⟨u, hu, hru⟩ := (isRoot_iff α β hα (S i) t).mp hti
    obtain ⟨v, hv, hrv⟩ := (isRoot_iff α β hα (S j) t).mp htj
    have huv := hroot (havoid i hi u hu) (havoid j hj v hv) (hru.trans hrv.symm)
    have hpair := hdisj (mem_sdiff.mp hi).1 (mem_sdiff.mp hj).1 hij
    have huj : u ∈ S j := by rw [huv]; exact hv
    exact disjoint_left.mp hpair hu huj

/-- Both regular-window assumptions of the source; the stronger theorem needs only the first. -/
theorem companion_T20_5 {ι : Type*} [DecidableEq ι]
    (x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hrankx : Module.finrank F₂ (squareClassSpace x L) = L)
    (_hranky : Module.finrank F₂ (squareClassSpace y L) = L)
    (hdirect : Disjoint (squareClassSpace x L) (squareClassSpace y L))
    (α β : ℚ) (hα : α ≠ 0) (hline : (y : ℚ) = α * (x : ℚ) + β)
    (I : Finset ι) (S : ι → Finset (Coordinate L)) (hdisj : (↑I : Set ι).PairwiseDisjoint S) :
    Conclusion L α β I S :=
  root_separation x y L hx hy (injective_evenMap_of_rank x L hrankx) hdirect α β hα hline I S hdisj

end PaperP1.OffsetRootPolynomials
