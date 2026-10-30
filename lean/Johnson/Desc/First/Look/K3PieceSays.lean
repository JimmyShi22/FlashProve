-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3PieceSays.lean: what a piece of the rule of composition says where it says
yes, as a statement on the piece and a «decide» at letters. One definition and one small statement.
It stands over the rule of composition alone. NO SOUNDNESS IS CLAIMED.

Why a file of its own. Every road from a kind's own text to the rule's GoodIn takes this statement
as a premise; it reads nothing of the oracle messages' signature.

Main names.
  PieceHears p decide: where the piece says yes, the work has passed; the oracles behind are what
    the stage leaves; every word of the rounds that «decide» is shown (the transcript's, without the
    sealed digest) is below the prime; and «decide» says yes at these rounds, from the record in
    front to the record behind.
  viewRounds_noDigest: striking the sealed digest turns no element that is sent or drawn.
Limits. A definition: that a piece has it is a theorem elsewhere. The oracles behind are written
out: (a.2.1, sLeft C (stg Fr p.base p.ds) a.2 τ) is what Johnson/Desc/Sound/StringsStay.lean
abbreviates as «behind».
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.StageCut
import Johnson.Top.H.K3LawClaims
import Johnson.Top.H.K3LawKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.Sound

/-- **What a piece says where it says yes**: where the piece says yes, the work has passed; the
oracles behind are what the stage leaves; every word of the rounds that «decide» is shown (the
transcript's, without the sealed digest) is below the prime; and «decide» says yes at these rounds,
from the record in front to the record behind. -/
def PieceHears {S Cl W : Type} {Fr : Frame} (p : Piece (ckP .two) Fr S Cl W)
    (decide : S → List Fmt.RoundView → List (List (ℕ × List UInt64)) → Except String S) : Prop :=
  ∀ a τ a', p.ior.red.out a τ = some a' →
    passT (ckP .two) p.ds (Maker.rhoT (ckP .two) p.ds τ) = true ∧
      a'.2 = (a.2.1, sLeft (ckP .two) (stg Fr p.base p.ds) a.2 τ) ∧
      okRoundsE ((rvT (ckP .two) p.ds τ).map Desc.noDigest) = true ∧
      ∃ cols, decide a.1 ((rvT (ckP .two) p.ds τ).map Desc.noDigest) cols = .ok a'.1

/-- Striking the sealed digest turns no element that is sent or drawn. -/
theorem viewRounds_noDigest (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)) :
    ((rvT (ckP .two) ds τ).map Desc.noDigest).map (rdRV Reading.gl) = viewRounds ds τ := by
  rw [List.map_map]
  exact List.map_congr_left fun r _ => rfl

#print axioms viewRounds_noDigest

end VerifiableInference.OnPublicFiles
