-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LocReadAt.lean: the carriage of "LOC"'s written round, GENERAL IN THE RECORD
AND IN THE BLOCK: what loc_goodIn4 (Johnson/Desc/K14/Law/GoodLoc.lean) shows inside its proof at the
shared chain's own record, cut out as a lemma: for whoever calls loc_core
(Johnson/Desc/K14/Law/RowsCore.lean) at another record.

  posAt        the piece that holds a block at one written round that draws t positions below 2 ^ a:
               no round is laid behind; the errors are the written count that bears e.
  pos_reads    **at a yes the written round reads as one typed draw of a list of positions, the one
               that the block reads.**
What is not claimed. PREMISE: the written round draws t positions below 2 ^ a and no element
(SendsDraws). No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.GoodLoc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block noDigest)
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run.PQ (CK)

variable {T Cl W : Type} {F : Frame}

/-- The piece that holds a block at one written round that draws t positions below 2 ^ a. -/
def posAt (b : Block T Cl) (base : Nat) (d : RDT) (a t e : Nat)
    (ext : T × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W) : Piece (ckP .two) F T Cl W :=
  ⟨b, base, [d], [], ext, (posMaps d a t).err ((e, ()) : Nat × Unit)⟩

/-- **The written round reads as one typed draw, the one that the block reads.** -/
theorem pos_reads (b : Block T Cl) (base : Nat) (d : RDT) {ns n a : Nat}
    (hd : SendsDraws (toRD d) ns 0 n a) (e : Nat)
    (ext : T × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W) :
    ∀ x τ x' r4, (posAt (F := F) b base d a n e ext).ior.red.out x τ = some x' →
      (rvT (ckP .two) [d] τ ++ []).map noDigest = [r4] →
      ∃ Q, (posMaps d a n).carry.tr τ = some (((), ()), Q, ()) ∧
        r4.drawn.poss = List.ofFn fun i => (Q i).val := by
  intro x τ x' r4 hout hr
  have ht := piece_tests _ x τ x' hout
  simp only [sTests, Bool.and_eq_true] at ht
  have hp : (posMaps d a n).pass τ = true := (posMaps_pass d _ _ τ).trans ht.1.1
  obtain ⟨m, c, ⟨⟩⟩ := τ
  have hr' : [noDigest (shownAt d m c)] = [r4] := hr
  obtain rfl := (List.cons.inj hr').1
  exact ⟨gPos a n _ (valsOf (toRD d) c), (posMaps d a n).tr_of_pass (m, c, ()) hp,
    poss_shown hd m c⟩

end Desc.K14.Law
