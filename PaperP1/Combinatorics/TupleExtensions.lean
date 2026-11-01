module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

/-! # Actual finite families of ordered tuple extensions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TupleExtensions

open Finset

abbrev append {s : ℕ} (x : Fin s → ℕ) (z : ℕ) : Fin (s + 1) → ℕ := Fin.snoc x z

def step {s : ℕ} (G : Finset ℕ) (F : Finset (Fin s → ℕ)) : Finset (Fin (s + 1) → ℕ) :=
  F.biUnion fun x ↦ G.image (append x)

theorem mem_step {s : ℕ} (G : Finset ℕ) (F : Finset (Fin s → ℕ)) (y : Fin (s + 1) → ℕ) :
    y ∈ step G F ↔ ∃ x ∈ F, ∃ z ∈ G, append x z = y := by
  simp only [step, mem_biUnion, mem_image]

theorem appended_disjoint {s : ℕ} (G : Finset ℕ) {x y : Fin s → ℕ} (hxy : x ≠ y) :
    Disjoint (G.image (append x)) (G.image (append y)) := by
  apply disjoint_left.mpr
  intro v hvx hvy
  obtain ⟨z, _, hzx⟩ := mem_image.mp hvx
  obtain ⟨w, _, hwy⟩ := mem_image.mp hvy
  apply hxy
  funext i
  have h := congrFun (hzx.trans hwy.symm) i.castSucc
  simpa only [append, Fin.snoc_castSucc] using h

theorem step_sum {s : ℕ} (G : Finset ℕ) (F : Finset (Fin s → ℕ)) (w : (Fin (s + 1) → ℕ) → ℝ) :
    (∑ y ∈ step G F, w y) = ∑ x ∈ F, ∑ z ∈ G, w (append x z) := by
  rw [step, sum_biUnion (fun _ _ _ _ hxy ↦ appended_disjoint G hxy)]
  apply sum_congr rfl
  intro x _
  apply sum_image
  intro z _ v _ h
  have heq := congrFun h (Fin.last s)
  simpa only [append, Fin.snoc_last] using heq

def more {s : ℕ} (G : Finset ℕ) (F : Finset (Fin s → ℕ)) : (k : ℕ) → Finset (Fin (s + k) → ℕ)
  | 0 => F
  | k + 1 => step G (more G F k)

def initial {s : ℕ} : (k : ℕ) → (Fin (s + k) → ℕ) → (Fin s → ℕ)
  | 0, x => x
  | k + 1, x => initial k (Fin.init x)

theorem step_coordinates {s : ℕ} (G : Finset ℕ) (F : Finset (Fin s → ℕ))
    (hF : ∀ x ∈ F, ∀ i, x i ∈ G) : ∀ y ∈ step G F, ∀ i, y i ∈ G := by
  intro y hy i
  obtain ⟨x, hx, z, hz, rfl⟩ := (mem_step G F y).mp hy
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [append, Fin.snoc_last] using hz
  · simpa only [append, Fin.snoc_castSucc] using hF x hx j

theorem more_coordinates {s : ℕ} (G : Finset ℕ) (F : Finset (Fin s → ℕ))
    (hF : ∀ x ∈ F, ∀ i, x i ∈ G) (k : ℕ) : ∀ y ∈ more G F k, ∀ i, y i ∈ G := by
  induction k with
  | zero => exact hF
  | succ k ih => exact step_coordinates G (more G F k) ih

theorem mem_more {s : ℕ} (G : Finset ℕ) (F : Finset (Fin s → ℕ))
    (hF : ∀ x ∈ F, ∀ i, x i ∈ G) (k : ℕ) (y : Fin (s + k) → ℕ) :
    y ∈ more G F k ↔ initial k y ∈ F ∧ ∀ i, y i ∈ G := by
  induction k with
  | zero => exact ⟨fun hy ↦ ⟨hy, hF y hy⟩, And.left⟩
  | succ k ih =>
    constructor
    · intro hy
      obtain ⟨x, hx, z, hz, rfl⟩ := (mem_step G (more G F k) y).mp hy
      refine ⟨?_, more_coordinates G F hF (k + 1) _ hy⟩
      simpa only [initial, append, Fin.init_snoc] using (ih x).mp hx |>.1
    · rintro ⟨hinitial, hcoords⟩
      apply (mem_step G (more G F k) y).mpr
      refine ⟨Fin.init y, (ih _).mpr ⟨hinitial, fun i ↦ hcoords i.castSucc⟩,
        y (Fin.last (s + k)), hcoords _, ?_⟩
      exact Fin.snoc_init_self y

def distinctMore {s : ℕ} (G : Finset ℕ) (F : Finset (Fin s → ℕ)) (k : ℕ) :
    Finset (Fin (s + k) → ℕ) := by
  classical
  exact (more G F k).filter Function.Injective

theorem mem_distinctMore {s : ℕ} (G : Finset ℕ) (F : Finset (Fin s → ℕ))
    (hF : ∀ x ∈ F, ∀ i, x i ∈ G) (k : ℕ) (y : Fin (s + k) → ℕ) :
    y ∈ distinctMore G F k ↔ initial k y ∈ F ∧ (∀ i, y i ∈ G) ∧ Function.Injective y := by
  classical
  rw [distinctMore, mem_filter, mem_more G F hF k y]
  exact and_assoc

end PaperP1.TupleExtensions
