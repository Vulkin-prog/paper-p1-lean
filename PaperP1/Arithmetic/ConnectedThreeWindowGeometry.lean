module

public import PaperP1.Arithmetic.ConnectedValueUnions
public import PaperP1.Model.PrivateNormalizedFamilies
public import Mathlib.Tactic.FinCases

/-! # Three normalized windows with connected overlaps lie in one fixed logarithmic interval -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedThreeWindowGeometry

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.ConnectedValueUnions PaperP1.PrivateNormalizedFamilies

theorem common_point_connected {ι : Type*} [Nonempty ι] (A : ι → Finset ℕ)
    (a : ℕ) (ha : ∀ i, a ∈ A i) : (intersectionGraph A).Connected := by
  constructor
  intro i j
  by_cases hij : i = j
  · subst j
    exact SimpleGraph.Reachable.rfl
  · exact (show (intersectionGraph A).Adj i j from ⟨hij, ⟨a, mem_inter.mpr ⟨ha i, ha j⟩⟩⟩).reachable

theorem three_edges (G : SimpleGraph (Fin 3)) (hG : G.Connected) :
    (G.Adj 0 1 ∧ G.Adj 0 2) ∨ (G.Adj 0 1 ∧ G.Adj 1 2) ∨ (G.Adj 0 2 ∧ G.Adj 1 2) := by
  have h0 : G.Adj 0 1 ∨ G.Adj 0 2 := by
    obtain ⟨j, hj⟩ := hG.preconnected.exists_adj_of_nontrivial 0
    fin_cases j
    · exact False.elim (G.irrefl hj)
    · exact Or.inl hj
    · exact Or.inr hj
  have h1 : G.Adj 0 1 ∨ G.Adj 1 2 := by
    obtain ⟨j, hj⟩ := hG.preconnected.exists_adj_of_nontrivial 1
    fin_cases j
    · exact Or.inl hj.symm
    · exact False.elim (G.irrefl hj)
    · exact Or.inr hj
  have h2 : G.Adj 0 2 ∨ G.Adj 1 2 := by
    obtain ⟨j, hj⟩ := hG.preconnected.exists_adj_of_nontrivial 2
    fin_cases j
    · exact Or.inl hj.symm
    · exact Or.inr hj.symm
    · exact False.elim (G.irrefl hj)
  tauto

theorem normalized_radius {Q c x L n : ℕ} (hc : c ≤ Q) (hx : 0 < x) (hn : n ∈ normalized c x L) :
    c * x ≤ n + Q * (L + 1) ∧ n ≤ c * x + Q * (L + 1) := by
  obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
  have hmI := mem_Ico.mp ((values_eq_interval hx).symm ▸ hm)
  have hlo := Nat.mul_le_mul_left c (show x ≤ m + 1 by omega)
  have hhi := Nat.mul_le_mul_left c (show m ≤ x + L by omega)
  rw [Nat.mul_add, Nat.mul_one] at hlo
  rw [Nat.mul_add] at hhi
  have hstep : c ≤ Q * (L + 1) := hc.trans (by nlinarith only [Nat.zero_le (Q * L)])
  have hlength := Nat.mul_le_mul hc (show L ≤ L + 1 by omega)
  exact ⟨by omega, by omega⟩

theorem adjacent_origins {Q L : ℕ} (c X : Fin 3 → ℕ) (hc : ∀ i, c i ≤ Q) (hX : ∀ i, 0 < X i)
    {i j : Fin 3} (hij : (intersectionGraph (fun i ↦ normalized (c i) (X i) L)).Adj i j) :
    c i * X i ≤ c j * X j + 2 * (Q * (L + 1)) ∧ c j * X j ≤ c i * X i + 2 * (Q * (L + 1)) := by
  obtain ⟨n, hn⟩ := hij.2
  have hi := normalized_radius (hc i) (hX i) (mem_inter.mp hn).1
  have hj := normalized_radius (hc j) (hX j) (mem_inter.mp hn).2
  omega

theorem connected_origins {Q L : ℕ} (c X : Fin 3 → ℕ) (hc : ∀ i, c i ≤ Q) (hX : ∀ i, 0 < X i)
    (hconn : (intersectionGraph (fun i ↦ normalized (c i) (X i) L)).Connected) :
    ∀ i, c 0 * X 0 ≤ c i * X i + 4 * (Q * (L + 1)) ∧ c i * X i ≤ c 0 * X 0 + 4 * (Q * (L + 1)) := by
  rcases three_edges _ hconn with ⟨h01, h02⟩ | ⟨h01, h12⟩ | ⟨h02, h12⟩
  · have h01b := adjacent_origins c X hc hX h01
    have h02b := adjacent_origins c X hc hX h02
    intro i
    fin_cases i <;> norm_num at * <;> omega
  · have h01b := adjacent_origins c X hc hX h01
    have h12b := adjacent_origins c X hc hX h12
    intro i
    fin_cases i <;> norm_num at * <;> omega
  · have h02b := adjacent_origins c X hc hX h02
    have h12b := adjacent_origins c X hc hX h12
    intro i
    fin_cases i <;> norm_num at * <;> omega

theorem union_bounds {Q L : ℕ} (c X : Fin 3 → ℕ) (hc : ∀ i, c i ≤ Q) (hX : ∀ i, 0 < X i)
    (hconn : (intersectionGraph (fun i ↦ normalized (c i) (X i) L)).Connected)
    (n : ℕ) (hn : n ∈ valueUnion c X L) :
    c 0 * X 0 ≤ n + 5 * (Q * (L + 1)) ∧ n ≤ c 0 * X 0 + 5 * (Q * (L + 1)) := by
  obtain ⟨i, _, hn⟩ := mem_biUnion.mp hn
  have hi := connected_origins c X hc hX hconn i
  have hnB := normalized_radius (hc i) (hX i) hn
  omega

theorem interval_data {N Q L : ℕ} (hN : 2 ≤ N) (c X : Fin 3 → ℕ)
    (hcpos : ∀ i, 0 < c i) (hc : ∀ i, c i ≤ Q) (hX : ∀ i, X i ∈ dyadicBlock N)
    (hconn : (intersectionGraph (fun i ↦ normalized (c i) (X i) L)).Connected)
    (hthin : 40 * (Q * (L + 1)) ≤ N) :
    let U := c 0 * X 0 - 5 * (Q * (L + 1))
    valueUnion c X L ⊆ Icc U (U + 10 * (Q * (L + 1))) ∧ N ≤ 2 * U ∧ U ≤ 2 * Q * N := by
  dsimp only
  have hXpos (i : Fin 3) : 0 < X i := by have hh := (mem_Ico.mp (hX i)).1; omega
  have hlow : N ≤ c 0 * X 0 := by
    have hh : X 0 ≤ c 0 * X 0 := by
      simpa only [one_mul] using Nat.mul_le_mul_right (X 0) (show 1 ≤ c 0 by have hh := hcpos 0; omega)
    exact (mem_Ico.mp (hX 0)).1.trans hh
  have hhigh : c 0 * X 0 ≤ 2 * Q * N := by
    have hh := Nat.mul_le_mul (hc 0) (mem_Ico.mp (hX 0)).2.le
    nlinarith only [hh]
  have hsize : 5 * (Q * (L + 1)) ≤ c 0 * X 0 := by omega
  have hcancel := Nat.sub_add_cancel hsize
  refine ⟨?_, by omega, (Nat.sub_le _ _).trans hhigh⟩
  intro n hn
  have hh := union_bounds c X hc hXpos hconn n hn
  exact mem_Icc.mpr ⟨by omega, by omega⟩

end PaperP1.ConnectedThreeWindowGeometry
