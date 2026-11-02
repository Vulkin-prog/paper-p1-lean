module

public import PaperP1.Arithmetic.PrivateEvenIntersection
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Even images of a connected union of value sets equal the sum of their local spaces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedValueUnions

open Finset PaperP1.Arithmetic PaperP1.FiniteEvenSquareClasses

variable {ι : Type*} [Fintype ι]

def intersectionGraph (A : ι → Finset ℕ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (A i ∩ A j).Nonempty
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, by rw [inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

theorem difference_mem {S : Finset ℕ} {n a : ℕ} (hn : n ∈ S) (ha : a ∈ S) :
    parityVec n - parityVec a ∈ space S := by
  rw [space_eq_span S a ha]
  exact Submodule.subset_span ⟨n, hn, rfl⟩

omit [Fintype ι] in
theorem propagate (A : ι → Finset ℕ) (a : ℕ)
    {i j : ι} (hij : (intersectionGraph A).Adj i j)
    (hi : ∀ n ∈ A i, parityVec n - parityVec a ∈ (⨆ k, space (A k) : Submodule F₂ (ℕ →₀ F₂))) :
    ∀ n ∈ A j, parityVec n - parityVec a ∈ (⨆ k, space (A k) : Submodule F₂ (ℕ →₀ F₂)) := by
  obtain ⟨b, hb⟩ := hij.2
  obtain ⟨hbi, hbj⟩ := mem_inter.mp hb
  intro n hn
  have hfirst := (le_iSup (fun k ↦ space (A k)) j) (difference_mem hn hbj)
  have hsecond := hi b hbi
  have heq : parityVec n - parityVec a = (parityVec n - parityVec b) + (parityVec b - parityVec a) := by abel
  rw [heq]
  exact Submodule.add_mem _ hfirst hsecond

theorem connected_union_space (A : ι → Finset ℕ) (hne : ∀ i, (A i).Nonempty)
    (hconn : (intersectionGraph A).Connected) :
    space (univ.biUnion A) = (⨆ i, space (A i) : Submodule F₂ (ℕ →₀ F₂)) := by
  classical
  obtain ⟨i₀⟩ := hconn.nonempty
  obtain ⟨a, ha⟩ := hne i₀
  let T : Submodule F₂ (ℕ →₀ F₂) := ⨆ i, space (A i)
  let P : ι → Prop := fun i ↦ ∀ n ∈ A i, parityVec n - parityVec a ∈ T
  have hbase : P i₀ := fun n hn ↦ (le_iSup (fun k ↦ space (A k)) i₀) (difference_mem hn ha)
  have hwalk {i j : ι} (p : (intersectionGraph A).Walk i j) : P i → P j := by
    induction p with
    | nil => exact fun hh ↦ hh
    | cons hij p ih => exact fun hh ↦ ih (propagate A a hij hh)
  have hall (i : ι) : P i := by
    obtain ⟨p⟩ := hconn i₀ i
    exact hwalk p hbase
  have haU : a ∈ univ.biUnion A := mem_biUnion.mpr ⟨i₀, mem_univ _, ha⟩
  apply le_antisymm
  · rw [space_eq_span _ a haU]
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨n, hn, rfl⟩ := hz
    obtain ⟨i, _hi, hni⟩ := mem_biUnion.mp hn
    exact hall i n hni
  · apply iSup_le
    intro i
    exact PrivateEvenIntersection.space_mono (subset_biUnion_of_mem A (mem_univ i))

end PaperP1.ConnectedValueUnions
