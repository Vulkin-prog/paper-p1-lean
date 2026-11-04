module

public import PaperP1.Model.PositionalDeletedFields
public import PaperP1.Probability.PositionalDeletionSupport

/-! # The actual original and deleted laws stay on their original dyadic ground -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalDeletedSupport

open Finset PaperP1.PositionalDeletedFields PaperP1.PositionalGroundSupport

theorem original_supported (G : Finset ℕ) (L : ℕ) : Supported G (original G L) :=
  supported_law G _ _

theorem once_supported (E : Finset (Finset ℕ)) (G : Finset ℕ) (L : ℕ) :
    Supported G (onceLaw E G L) :=
  PositionalDeletionSupport.supported_once G E _ (original_supported G L)

theorem isolated_supported (E : Finset (Finset ℕ)) (G : Finset ℕ) (L : ℕ) :
    Supported G (isolatedLaw E G L) :=
  PositionalDeletionSupport.supported_isolated G E _ (original_supported G L)

end PaperP1.PositionalDeletedSupport
