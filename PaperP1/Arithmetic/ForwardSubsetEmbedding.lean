module

public import PaperP1.Arithmetic.ForwardSubsetSelections

/-! # Actual finite subsets embed into their forward envelopes by physical value -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ForwardSubsetEmbedding

open Finset

def index (U H : ℕ) (V : Finset ℕ) (hV : V ⊆ Ico U (U + H)) : V ↪ Fin H where
  toFun n := ⟨n.val - U, by have hh := mem_Ico.mp (hV n.property); omega⟩
  inj' := by
    intro n m he
    have hn := mem_Ico.mp (hV n.property)
    have hm := mem_Ico.mp (hV m.property)
    have hh := congrArg Fin.val he
    apply Subtype.ext
    dsimp at hh
    omega

theorem label (U H : ℕ) (V : Finset ℕ) (hV : V ⊆ Ico U (U + H)) (n : V) :
    U + (index U H V hV n).val = n.val := by
  have hh := mem_Ico.mp (hV n.property)
  dsimp [index]
  omega

end PaperP1.ForwardSubsetEmbedding
