module

public import PaperP1.Arithmetic.CertificatePairs
public import PaperP1.Arithmetic.ProjectedWindowCounts

/-! # Actual list classes with a new or fixed-old certificate receiver -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HalfCountCertificateLists

open Finset PaperP1.ProjectedWindowLists PaperP1.AnchorCertificateGraph

def newReceiverLists {r s : ℕ} (G P : Finset ℕ) (X W t : ℕ) (Y : ℝ)
    (old : Fin s → ℕ) : Finset (Fin (r + 1) → ℕ) := by
  classical
  exact (lists G W old).filter fun n ↦ ∃ i, ∃ j : Fin r,
    (n i, n (i.succAbove j)) ∈ PaperP1.CertificatePairs.pairs P G X W t Y

def oldReceiverLists {r s : ℕ} (G : Finset ℕ) (X W t : ℕ) (Y : ℝ)
    (old : Fin s → ℕ) : Finset (Fin (r + 1) → ℕ) := by
  classical
  exact (lists G W old).filter fun n ↦ ∃ i, ∃ k : Fin s,
    n i ∈ incoming G X W t Y (old k)

theorem no_new_receiver {s : ℕ} (G P : Finset ℕ) (X W t : ℕ) (Y : ℝ) (old : Fin s → ℕ) :
    newReceiverLists (r := 0) G P X W t Y old = ∅ := by
  classical
  ext n
  simp only [newReceiverLists, mem_filter, Fin.exists_fin_zero, exists_false, and_false, notMem_empty]

theorem new_receiver_bound {r s : ℕ} (G P : Finset ℕ) (X W t : ℕ) (Y D B : ℝ)
    (old : Fin s → ℕ) (hP : P ⊆ G)
    (hD : ∀ x ∈ P, ((outgoing G X W t Y x).card : ℝ) ≤ D)
    (hB : ∀ x ∈ G, ∀ y ∈ G,
      ((lists (r := r) G W (Fin.cons y (Fin.cons x old))).card : ℝ) ≤ B)
    (hBnonneg : 0 ≤ B) :
    ((newReceiverLists (r := r + 1) G P X W t Y old).card : ℝ) ≤
      (((r + 2) * (r + 1) : ℕ) : ℝ) * ((P.card : ℝ) * D * B) := by
  classical
  let Q := PaperP1.CertificatePairs.pairs P G X W t Y
  let F := fun p : Fin (r + 2) × Fin (r + 1) ↦
    (lists (r := r + 2) G W old).filter fun n ↦ (n p.1, n (p.1.succAbove p.2)) ∈ Q
  have hcover : ∀ n ∈ newReceiverLists (r := r + 1) G P X W t Y old,
      ∃ p ∈ (univ : Finset (Fin (r + 2) × Fin (r + 1))), n ∈ F p := by
    intro n hn
    obtain ⟨hnL, i, j, hij⟩ := mem_filter.mp hn
    exact ⟨(i, j), mem_univ _, mem_filter.mpr ⟨hnL, hij⟩⟩
  have hQ := PaperP1.CertificatePairs.cardinal_bound P G X W t Y D hD
  have hF : ∀ p ∈ (univ : Finset (Fin (r + 2) × Fin (r + 1))),
      ((F p).card : ℝ) ≤ (P.card : ℝ) * D * B := by
    intro p _
    have hb : ∀ q ∈ Q, ((lists (r := r) G W (Fin.cons q.2 (Fin.cons q.1 old))).card : ℝ) ≤ B := by
      intro q hq
      have hd := PaperP1.CertificatePairs.pair_data P G X W t Y q hq
      exact hB q.1 (hP hd.1) q.2 hd.2.1
    have hc := PaperP1.ProjectedWindowCounts.pair_bound G W old p.1 p.2 Q B hb
    exact hc.trans (mul_le_mul_of_nonneg_right hQ hBnonneg)
  have hc := PaperP1.FiniteCoverCount.cardinal_le
    (newReceiverLists (r := r + 1) G P X W t Y old)
    (univ : Finset (Fin (r + 2) × Fin (r + 1))) F _ hcover hF
  simpa only [card_univ, Fintype.card_prod, Fintype.card_fin] using hc

theorem old_receiver_bound {r s : ℕ} (G : Finset ℕ) (X W t : ℕ) (Y D B : ℝ)
    (old : Fin s → ℕ) (hD : ∀ k, ((incoming G X W t Y (old k)).card : ℝ) ≤ D)
    (hB : ∀ x ∈ G, ((lists (r := r) G W (Fin.cons x old)).card : ℝ) ≤ B)
    (hBnonneg : 0 ≤ B) :
    ((oldReceiverLists (r := r) G X W t Y old).card : ℝ) ≤
      (((r + 1) * s : ℕ) : ℝ) * (D * B) := by
  classical
  let F := fun p : Fin (r + 1) × Fin s ↦
    (lists (r := r + 1) G W old).filter fun n ↦ n p.1 ∈ incoming G X W t Y (old p.2)
  have hcover : ∀ n ∈ oldReceiverLists (r := r) G X W t Y old,
      ∃ p ∈ (univ : Finset (Fin (r + 1) × Fin s)), n ∈ F p := by
    intro n hn
    obtain ⟨hnL, i, k, hik⟩ := mem_filter.mp hn
    exact ⟨(i, k), mem_univ _, mem_filter.mpr ⟨hnL, hik⟩⟩
  have hF : ∀ p ∈ (univ : Finset (Fin (r + 1) × Fin s)), ((F p).card : ℝ) ≤ D * B := by
    intro p _
    have hb : ∀ x ∈ incoming G X W t Y (old p.2),
        ((lists (r := r) G W (Fin.cons x old)).card : ℝ) ≤ B := fun x hx ↦ hB x (mem_filter.mp hx).1
    exact (PaperP1.ProjectedWindowCounts.coordinate_bound G W old p.1 _ B hb).trans
      (mul_le_mul_of_nonneg_right (hD p.2) hBnonneg)
  have hc := PaperP1.FiniteCoverCount.cardinal_le (oldReceiverLists (r := r) G X W t Y old)
    (univ : Finset (Fin (r + 1) × Fin s)) F _ hcover hF
  simpa only [card_univ, Fintype.card_prod, Fintype.card_fin] using hc

end PaperP1.HalfCountCertificateLists
