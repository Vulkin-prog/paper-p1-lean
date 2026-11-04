module

public import PaperP1.Arithmetic.AnchoredWindowPivots
public import PaperP1.Model.AnchoredPrivateForcing

/-! # Every admissible arithmetic anchor has an actual full conditional forcing

The anchor is chosen before the prime signs. It may be the unique vertex
with a small pivot. All other pivots exceed the word length and preserve
the anchor's raw value and the full small-prime environment.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredWindowForcing

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.PrivatePrimeForcing PaperP1.AnchoredPrivateValues PaperP1.UniformFubini
  PaperP1.SmallPrimeConditioning PaperP1.OddPrimePivot

local instance anchoredWindowForcingDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

def smallVertices (j B Y : ℕ) : Finset (Fin B) :=
  univ.filter fun i ↦ largestOddPrime (j + i.val) ≤ Y

theorem anchor_rule_iff {j B Y : ℕ} (anchor : Fin B) :
    (∀ i : Fin B, largestOddPrime (j + i.val) ≤ Y → i = anchor) ↔
      ∀ i : Free anchor, Y < largestOddPrime (j + i.val.val) := by
  constructor
  · intro h i
    by_contra hn
    exact i.property (h i.val (le_of_not_gt hn))
  · intro h i hi
    by_contra hn
    exact (not_lt_of_ge hi) (h ⟨i, hn⟩)

theorem exists_anchor {j B Y : ℕ} (hB : 0 < B) (hsmall : (smallVertices j B Y).card ≤ 1) :
    ∃ anchor : Fin B, ∀ i : Fin B, largestOddPrime (j + i.val) ≤ Y → i = anchor := by
  by_cases hs : (smallVertices j B Y).Nonempty
  · obtain ⟨anchor, ha⟩ := hs
    refine ⟨anchor, ?_⟩
    intro i hi
    exact card_le_one.mp hsmall i (mem_filter.mpr ⟨mem_univ _, hi⟩) anchor ha
  · refine ⟨⟨0, hB⟩, ?_⟩
    intro i hi
    exact (hs ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩).elim

theorem small_card_mono {j B Bmax Y : ℕ} (hB : B ≤ Bmax) :
    (smallVertices j B Y).card ≤ (smallVertices j Bmax Y).card := by
  apply card_le_card_of_injOn (fun i : Fin B ↦ Fin.castLE hB i)
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩
  · intro i _ k _ he
    apply Fin.ext
    exact congrArg (fun z : Fin Bmax ↦ z.val) he

theorem maximal_retention_has_anchor {j B Bmax Y : ℕ} (hBpos : 0 < B) (hB : B ≤ Bmax)
    (hsmall : (smallVertices j Bmax Y).card ≤ 1) :
    ∃ anchor : Fin B, ∀ i : Fin B, largestOddPrime (j + i.val) ≤ Y → i = anchor :=
  exists_anchor hBpos ((small_card_mono hB).trans hsmall)

structure Data (M j B Y : ℕ) (anchor : Fin B) : Prop where
  boundary_pos : 0 < j
  cutoff : j + B ≤ M + 1
  small_pos : 1 ≤ Y
  word_width : B ≤ Y
  good : ∀ i : Free anchor, Y < largestOddPrime (j + i.val.val)

theorem data_of_anchor_rule {M j B Y : ℕ} (anchor : Fin B)
    (hj : 0 < j) (hcut : j + B ≤ M + 1) (hY : 1 ≤ Y) (hBY : B ≤ Y)
    (hrule : ∀ i : Fin B, largestOddPrime (j + i.val) ≤ Y → i = anchor) :
    Data M j B Y anchor :=
  ⟨hj, hcut, hY, hBY, (anchor_rule_iff anchor).mp hrule⟩

variable {M j B Y : ℕ} {anchor : Fin B}

def pivots (D : Data M j B Y anchor) : Free anchor → PrimeUpTo M :=
  AnchoredWindowPivots.pivots D.boundary_pos D.cutoff anchor
    (fun i ↦ D.small_pos.trans_lt (D.good i))

theorem private_basis (D : Data M j B Y anchor) (i : Free anchor) :
    valueSystem M (relativeValues (fun k : Fin B ↦ j + k.val) anchor)
      (Pi.single (pivots D i) 1) = Pi.single i 1 :=
  AnchoredWindowPivots.basis D.boundary_pos D.cutoff anchor _
    (fun k ↦ D.word_width.trans (D.good k).le) i

def force (D : Data M j B Y anchor) (b : Fin B → F₂) (ω : SampleSpace M) : SampleSpace M :=
  AnchoredPrivateForcing.force (fun k : Fin B ↦ j + k.val) anchor (pivots D) b ω

theorem hits (D : Data M j B Y anchor) (b : Fin B → F₂) (ω : SampleSpace M) :
    ∃ s : F₂, valueSystem M (fun k : Fin B ↦ j + k.val) (force D b ω) = fun i ↦ b i + s :=
  AnchoredPrivateForcing.force_hits _ anchor (fun k ↦ by have := D.boundary_pos; omega)
    (pivots D) (private_basis D) b ω

theorem preserves_anchor (D : Data M j B Y anchor) (b : Fin B → F₂) (ω : SampleSpace M) :
    valueBit (force D b ω) (j + anchor.val) = valueBit ω (j + anchor.val) := by
  apply AnchoredPrivateForcing.preserves_anchor
  intro i
  exact AnchoredWindowPivots.not_dvd_anchor D.boundary_pos D.cutoff anchor _
    (fun k ↦ D.word_width.trans (D.good k).le) i

theorem preserves_small (D : Data M j B Y anchor) (b : Fin B → F₂) (ω : SampleSpace M) :
    smallBits M Y (force D b ω) = smallBits M Y ω :=
  PrivateHardConditionalForcing.smallTrace_unchanged _ (pivots D) D.good _ ω

theorem actual_orientation (D : Data M j B Y anchor) (b : Fin B → F₂) (ω : SampleSpace M) :
    valueSystem M (fun k : Fin B ↦ j + k.val) (force D b ω) =
      fun i ↦ b i + (valueBit ω (j + anchor.val) - b anchor) := by
  apply AnchoredPrivateForcing.source_orientation _ anchor
    (fun k ↦ by have := D.boundary_pos; omega) (pivots D) (private_basis D)
  intro i
  exact AnchoredWindowPivots.not_dvd_anchor D.boundary_pos D.cutoff anchor _
    (fun k ↦ D.word_width.trans (D.good k).le) i

theorem full_conditional (D : Data M j B Y anchor) (b : Fin B → F₂) (f : SampleSpace M → ℝ) :
    average (fun ω ↦ f (force D b ω)) =
      average (fun ω ↦ if ∃ s : F₂,
        valueSystem M (fun k : Fin B ↦ j + k.val) ω = (fun i ↦ b i + s) then f ω else 0) /
        (2 ^ (B - 1) : ℝ)⁻¹ := by
  simpa only [Fintype.card_fin, force] using AnchoredPrivateForcing.uniform_conditional
    (fun k : Fin B ↦ j + k.val) anchor (fun k ↦ by have := D.boundary_pos; omega)
    (pivots D) (private_basis D) b f

theorem event_probability (D : Data M j B Y anchor) (b : Fin B → F₂) :
    average (fun ω : SampleSpace M ↦ if ∃ s : F₂,
      valueSystem M (fun k : Fin B ↦ j + k.val) ω = (fun i ↦ b i + s) then (1 : ℝ) else 0) =
        (2 ^ (B - 1) : ℝ)⁻¹ := by
  simpa only [Fintype.card_fin] using AnchoredPrivateForcing.event_probability
    (fun k : Fin B ↦ j + k.val) anchor (fun k ↦ by have := D.boundary_pos; omega)
    (pivots D) (private_basis D) b

end PaperP1.AnchoredWindowForcing
