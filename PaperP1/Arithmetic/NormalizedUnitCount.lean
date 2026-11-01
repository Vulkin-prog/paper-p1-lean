module

public import PaperP1.Arithmetic.NormalizedWindowSets
public import PaperP1.Arithmetic.ChannelCount

/-! # Exact normalized coincidences and the channel lattice-point bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedUnitCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets

def units (a b x y L : ℕ) : Finset (Fin (L + 1) × Fin (L + 1)) :=
  univ.filter fun u ↦ b * startCompleteVertexLabel x L u.1 = a * startCompleteVertexLabel y L u.2

def offset {L : ℕ} (v : Fin (L + 1)) : ℤ := (v.val : ℤ) - 1

theorem mem_units {a b x y L : ℕ} {u : Fin (L + 1) × Fin (L + 1)} :
    u ∈ units a b x y L ↔ b * startCompleteVertexLabel x L u.1 = a * startCompleteVertexLabel y L u.2 := by
  simp only [units, mem_filter, mem_univ, true_and]

theorem label_cast {x L : ℕ} (hx : 0 < x) (v : Fin (L + 1)) :
    (startCompleteVertexLabel x L v : ℤ) = (x : ℤ) + offset v := by
  rw [startCompleteVertexLabel_eq_offset hx]
  unfold offset
  omega

theorem offset_injective (L : ℕ) : Function.Injective (offset (L := L)) := by
  intro v w heq
  apply Fin.ext
  unfold offset at heq
  omega

theorem offset_mem_interval {L : ℕ} (v : Fin (L + 1)) : offset v ∈ Channels.offsetInterval L := by
  rw [Channels.mem_offsetInterval]
  unfold offset
  have hv := v.isLt
  omega

theorem normalized_intersection_card {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) :
    (normalized b x L ∩ normalized a y L).card = (units a b x y L).card := by
  symm
  apply card_bij (fun u _ ↦ b * startCompleteVertexLabel x L u.1)
  · intro u hu
    apply mem_inter.mpr
    refine ⟨mem_image.mpr ⟨_, mem_values.mpr ⟨u.1, rfl⟩, rfl⟩, ?_⟩
    exact mem_image.mpr ⟨_, mem_values.mpr ⟨u.2, rfl⟩, (mem_units.mp hu).symm⟩
  · intro u hu v hv heq
    have hleft : u.1 = v.1 := startCompleteVertexLabel_injective hx (mul_left_cancel₀ hb.ne' heq)
    have hright_eq : a * startCompleteVertexLabel y L u.2 = a * startCompleteVertexLabel y L v.2 :=
      (mem_units.mp hu).symm.trans (heq.trans (mem_units.mp hv))
    have hright : u.2 = v.2 := startCompleteVertexLabel_injective hy (mul_left_cancel₀ ha.ne' hright_eq)
    exact Prod.ext hleft hright
  · intro n hn
    obtain ⟨hnx, hny⟩ := mem_inter.mp hn
    change n ∈ (values x L).image (fun v ↦ b * v) at hnx
    change n ∈ (values y L).image (fun v ↦ a * v) at hny
    obtain ⟨nx, hxValues, hxEq⟩ := mem_image.mp hnx
    obtain ⟨ny, hyValues, hyEq⟩ := mem_image.mp hny
    obtain ⟨u, huEq⟩ := mem_values.mp hxValues
    obtain ⟨v, hvEq⟩ := mem_values.mp hyValues
    refine ⟨(u, v), mem_units.mpr ?_, ?_⟩
    · rw [huEq, hvEq]
      exact hxEq.trans hyEq.symm
    · change b * startCompleteVertexLabel x L u = n
      rw [huEq]
      exact hxEq

theorem units_card_le_channel {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y) :
    (units a b x y L).card ≤ (Channels.channelCells L b a ((a : ℤ) * y - (b : ℤ) * x)).card := by
  let f : Fin (L + 1) × Fin (L + 1) → ℤ × ℤ := fun u ↦ (offset u.1, offset u.2)
  have hf : Function.Injective f := by
    intro u v heq
    exact Prod.ext (offset_injective L (congrArg Prod.fst heq)) (offset_injective L (congrArg Prod.snd heq))
  rw [← card_image_of_injective (units a b x y L) hf]
  apply card_le_card
  intro c hc
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hc
  rw [Channels.mem_channelCells]
  refine ⟨Channels.mem_offsetBox.mpr ⟨Channels.mem_offsetInterval.mp (offset_mem_interval u.1),
    Channels.mem_offsetInterval.mp (offset_mem_interval u.2)⟩, ?_⟩
  have h := congrArg (fun n : ℕ ↦ (n : ℤ)) (mem_units.mp hu)
  push_cast at h
  rw [label_cast hx, label_cast hy] at h
  change (b : ℤ) * offset u.1 - (a : ℤ) * offset u.2 = (a : ℤ) * y - (b : ℤ) * x
  nlinarith

theorem intersection_card_bound {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 0 < x) (hy : 0 < y) :
    ((normalized b x L ∩ normalized a y L).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / b + 1 := by
  have hcard := units_card_le_channel (a := a) (b := b) (L := L) hx hy
  have hbound := Channels.channelCells_card_cast_le_secondStep L b a hb ha hab.symm ((a : ℤ) * y - (b : ℤ) * x)
  have hcardQ : ((units a b x y L).card : ℚ) ≤
      ((Channels.channelCells L b a ((a : ℤ) * y - (b : ℤ) * x)).card : ℚ) := by exact_mod_cast hcard
  have hQ : ((units a b x y L).card : ℚ) ≤ ((L + 1 : ℕ) : ℚ) / b + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one, Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_neg, Int.cast_one, sub_neg_eq_add] using hcardQ.trans hbound
  rw [normalized_intersection_card ha hb hx hy]
  have hR := (Rat.cast_le (K := ℝ)).mpr hQ
  norm_num only [Rat.cast_natCast, Rat.cast_add, Rat.cast_div, Rat.cast_one] at hR
  exact hR

end PaperP1.NormalizedUnitCount
