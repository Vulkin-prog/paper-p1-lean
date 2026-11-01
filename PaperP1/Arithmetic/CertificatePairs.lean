module

public import PaperP1.Arithmetic.AnchorCertificateGraph

/-! # Counting actual directed certificate pairs from outgoing degrees -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CertificatePairs

open Finset PaperP1.AnchorCertificateGraph

def pairs (P G : Finset ℕ) (X W t : ℕ) (Y : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact P.biUnion fun x ↦ (outgoing G X W t Y x).image (Prod.mk x)

theorem mem_pairs (P G : Finset ℕ) (X W t : ℕ) (Y : ℝ) (x y : ℕ) :
    (x, y) ∈ pairs P G X W t Y ↔ x ∈ P ∧ y ∈ outgoing G X W t Y x := by
  classical
  simp only [pairs, mem_biUnion, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, hax, hby⟩
    subst a
    subst b
    exact ⟨ha, hb⟩
  · rintro ⟨hx, hy⟩
    exact ⟨x, hx, y, hy, rfl, rfl⟩

theorem pair_data (P G : Finset ℕ) (X W t : ℕ) (Y : ℝ) (p : ℕ × ℕ)
    (hp : p ∈ pairs P G X W t Y) : p.1 ∈ P ∧ p.2 ∈ G ∧ Edge X W t Y p.1 p.2 := by
  classical
  obtain ⟨hx, hy⟩ := (mem_pairs P G X W t Y p.1 p.2).mp hp
  exact ⟨hx, (mem_filter.mp hy).1, (mem_filter.mp hy).2⟩

theorem cardinal_bound (P G : Finset ℕ) (X W t : ℕ) (Y D : ℝ)
    (hD : ∀ x ∈ P, ((outgoing G X W t Y x).card : ℝ) ≤ D) :
    ((pairs P G X W t Y).card : ℝ) ≤ (P.card : ℝ) * D := by
  classical
  let F := fun x ↦ (outgoing G X W t Y x).image (Prod.mk x)
  apply PaperP1.FiniteCoverCount.cardinal_le (pairs P G X W t Y) P F D
  · intro p hp
    exact mem_biUnion.mp hp
  · intro x hx
    exact (show ((F x).card : ℝ) ≤ (outgoing G X W t Y x).card by exact_mod_cast card_image_le).trans (hD x hx)

theorem outgoing_iff_incoming (G : Finset ℕ) (X W t : ℕ) (Y : ℝ) (x y : ℕ)
    (hx : x ∈ G) (hy : y ∈ G) :
    y ∈ outgoing G X W t Y x ↔ x ∈ incoming G X W t Y y := by
  classical
  simp only [outgoing, incoming, mem_filter, hx, hy, true_and]

end PaperP1.CertificatePairs
