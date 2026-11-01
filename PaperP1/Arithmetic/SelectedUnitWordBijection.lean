module

public import PaperP1.Arithmetic.SelectedUnitWords

/-! # Actual nonempty even unit selections are exactly their canonical endpoint words -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedUnitWordBijection

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount
  PaperP1.ChannelPlacements PaperP1.ExactUnitProgression PaperP1.ChannelGapWords
  PaperP1.SelectedUnitExtrema PaperP1.SelectedUnitWords

local instance selectedWordBijectionPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Encodings (a b x y L : ℕ) := Σ s : Shapes a b x y L, Words s.1.val

instance encodingsFintype (a b x y L : ℕ) : Fintype (Encodings a b x y L) := by
  unfold Encodings
  infer_instance

theorem shape_ext {a b x y L : ℕ} {s t : Shapes a b x y L}
    (hgap : s.1.val = t.1.val) (hfirst : s.2.val = t.2.val) : s = t := by
  rcases s with ⟨d, u⟩
  rcases t with ⟨e, v⟩
  have hde : d = e := Subtype.ext hgap
  subst e
  have huv : u = v := Subtype.ext hfirst
  subst v
  rfl

theorem shape_eq_of_selection_eq {a b x y L : ℕ} (ha : 0 < a) (hx : 0 < x) (hy : 0 < y)
    (s t : Shapes a b x y L) (ws : Words s.1.val) (wt : Words t.1.val)
    (h : selection hx hy s ws = selection hx hy t wt) : s = t := by
  let A := selectionBounds hx hy s ws
  let B := selectionBounds hx hy t wt
  have hmin₁ : s.2.val.val.1 ≤ t.2.val.val.1 :=
    A.first_le _ (h.symm ▸ first_mem_selection hx hy t wt)
  have hmin₂ : t.2.val.val.1 ≤ s.2.val.val.1 :=
    B.first_le _ (h ▸ first_mem_selection hx hy s ws)
  have hfirst : s.2.val = t.2.val := left_projection_injective ha hy (le_antisymm hmin₁ hmin₂)
  have hmax₁ : (step hx hy s (Fin.last s.1.val)).val.1 ≤ (step hx hy t (Fin.last t.1.val)).val.1 :=
    B.le_last _ (h ▸ last_mem_selection hx hy s ws)
  have hmax₂ : (step hx hy t (Fin.last t.1.val)).val.1 ≤ (step hx hy s (Fin.last s.1.val)).val.1 :=
    A.le_last _ (h.symm ▸ last_mem_selection hx hy t wt)
  have hmax := congrArg Fin.val (le_antisymm hmax₁ hmax₂)
  rw [step_left, step_left, Fin.val_last, Fin.val_last] at hmax
  have hfirstVal := congrArg (fun u : ↥(units a b x y L) ↦ u.val.1.val) hfirst
  have hmul : a * s.1.val = a * t.1.val := by omega
  exact shape_ext (Nat.eq_of_mul_eq_mul_left ha hmul) hfirst

theorem word_eq_of_selection_eq {a b x y L : ℕ} (ha : 0 < a) (hx : 0 < x) (hy : 0 < y)
    (s : Shapes a b x y L) (w v : Words s.1.val)
    (h : selection hx hy s w = selection hx hy s v) : w = v := by
  apply Subtype.ext
  funext k
  rw [← coefficient_at_step ha hx hy s w k, ← coefficient_at_step ha hx hy s v k, h]

theorem represent_selection {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) (S : Finset ↥(units a b x y L)) (hS : S.Nonempty) (heven : Even S.card) :
    ∃ s : Shapes a b x y L, ∃ w : Words s.1.val, selection (by omega) hy s w = S := by
  have hcard : 2 ≤ S.card := by
    have hp := card_pos.mpr hS
    obtain ⟨k, hk⟩ := heven
    omega
  let A := bounds S hS
  obtain ⟨d, hd, hleft, hright, hfitX, hfitY⟩ := canonical_gap ha hb hab hx hy hcard A
  let s : Shapes a b x y L := ⟨⟨d, hd⟩, ⟨A.first, hfitX, hfitY⟩⟩
  let f : Fin (d + 1) → F₂ := fun k ↦ BinaryEvenSelections.coefficients S (step (by omega) hy s k)
  have hcover : ∀ u ∈ S, ∃ k : Fin (d + 1), u = step (by omega) hy s k := by
    intro u hu
    exact selected_eq_stepUnit ha hab hx hy A hleft
      (fits_of_placement hfitX) (fits_of_placement hfitY) u hu
  have himage : (BinaryEvenSelections.selected f).image (step (by omega) hy s) = S := by
    ext u
    constructor
    · intro hu
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hu
      have hn : f k ≠ 0 := (mem_filter.mp hk).2
      by_contra hnot
      exact hn (by simp only [f, BinaryEvenSelections.coefficients, ite_eq_right hnot])
    · intro hu
      obtain ⟨k, hk⟩ := hcover u hu
      apply mem_image.mpr
      refine ⟨k, mem_filter.mpr ⟨mem_univ _, ?_⟩, hk.symm⟩
      dsimp only [f]
      rw [← hk]
      simp only [BinaryEvenSelections.coefficients, ite_eq_left hu, ne_eq, one_ne_zero, not_false_eq_true]
  have hfEven : Even (BinaryEvenSelections.selected f).card := by
    have hc := card_image_of_injective (BinaryEvenSelections.selected f) (step_injective ha (by omega) hy s)
    rw [himage] at hc
    exact hc ▸ heven
  have hsum : ∑ k, f k = 0 := by
    have hmem := (BinaryEvenSelections.even_selected_iff f).mp hfEven
    simpa only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply] using hmem
  have hroot : f 0 = 1 := by
    dsimp only [f]
    rw [step_zero]
    exact ite_eq_left A.first_mem
  have hlast : step (by omega) hy s (Fin.last d) = A.last := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · exact hleft.symm
    · exact hright.symm
  have htip : f (Fin.last d) = 1 := by
    dsimp only [f]
    rw [hlast]
    exact ite_eq_left A.last_mem
  exact ⟨s, ⟨f, hroot, htip, hsum⟩, himage⟩

def encode {a b x y L : ℕ} (ha : 0 < a) (hx : 0 < x) (hy : 0 < y) (e : Encodings a b x y L) :
    {S : Finset ↥(units a b x y L) // S.Nonempty ∧ Even S.card} :=
  ⟨selection hx hy e.1 e.2, ⟨_, first_mem_selection hx hy e.1 e.2⟩, selection_even ha hx hy e.1 e.2⟩

theorem encode_injective {a b x y L : ℕ} (ha : 0 < a) (hx : 0 < x) (hy : 0 < y) :
    Function.Injective (encode (b := b) (L := L) ha hx hy) := by
  rintro ⟨s, ws⟩ ⟨t, wt⟩ h
  have hsel := congrArg Subtype.val h
  change selection hx hy s ws = selection hx hy t wt at hsel
  have hst := shape_eq_of_selection_eq ha hx hy s t ws wt hsel
  subst t
  have hword := word_eq_of_selection_eq ha hx hy s ws wt hsel
  subst wt
  rfl

theorem encode_surjective {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) : Function.Surjective (encode (b := b) (x := x) (L := L) ha (by omega) hy) := by
  intro S
  obtain ⟨s, w, h⟩ := represent_selection ha hb hab hx hy S.val S.property.1 S.property.2
  exact ⟨⟨s, w⟩, Subtype.ext h⟩

def canonicalEquiv {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) :
    Encodings a b x y L ≃ {S : Finset ↥(units a b x y L) // S.Nonempty ∧ Even S.card} :=
  Equiv.ofBijective (encode ha (by omega) hy)
    ⟨encode_injective ha (by omega) hy, encode_surjective ha hb hab hx hy⟩

end PaperP1.SelectedUnitWordBijection
