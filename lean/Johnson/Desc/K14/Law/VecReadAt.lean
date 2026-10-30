-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/VecReadAt.lean: the carriage of a written round that draws a point, GENERAL IN
THE RECORD AND IN THE BLOCK: what point_goodIn (Johnson/Desc/K14/Law/PointGood.lean) and
zeta_goodIn7
(ZetaRead.lean) show inside their proofs at the shared chain's own record, cut out as a lemma: for
whoever calls point_core or fold_core at another record.

  vecAt        the piece that holds a block at one written round that draws n elements: no round is
               laid behind; the errors are the written count that bears e.
  vec_reads    **at a yes the written round reads as one typed draw of a point, the one that the
               block reads as drawn.**
What is not claimed. PREMISE: the written round draws n elements and no position (SendsDraws). No
soundness of a verifier.

-/
import Johnson.Desc.K14.Law.ZetaRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block noDigest)
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run.PQ (CK)

variable {T Cl W : Type} {F : Frame}

/-- The piece that holds a block at one written round that draws n elements. -/
def vecAt (b : Block T Cl) (base : Nat) (d : RDT) (n e : Nat)
    (ext : T × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W) : Piece (ckP .two) F T Cl W :=
  ⟨b, base, [d], [], ext, (vecMaps d n).err ((e, ()) : Nat × Unit)⟩

/-- **The written round reads as one typed draw, the one that the block reads.** -/
theorem vec_reads (b : Block T Cl) (base : Nat) (d : RDT) {ns n a0 : Nat}
    (hd : SendsDraws (toRD d) ns n 0 a0) (e : Nat)
    (ext : T × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W) :
    ∀ x τ x' r, (vecAt (F := F) b base d n e ext).ior.red.out x τ = some x' →
      (rvT (ckP .two) [d] τ ++ []).map noDigest = [r] →
      ∃ psi, (vecMaps d n).carry.tr τ = some (((), ()), psi, ()) ∧
        (drawn r).map OnBytes.Model.Reading.gl.val = List.ofFn psi := by
  intro x τ x' r hout hr
  have ht := piece_tests _ x τ x' hout
  simp only [sTests, Bool.and_eq_true] at ht
  have hp : (vecMaps d n).pass τ = true := (vecMaps_pass d _ τ).trans ht.1.1
  obtain ⟨m, c, ⟨⟩⟩ := τ
  have hr' : [noDigest (shownAt d m c)] = [r] := hr
  obtain rfl := (List.cons.inj hr').1
  exact ⟨gVec n _ (valsOf (toRD d) c), (vecMaps d n).tr_of_pass (m, c, ()) hp, drawn_shown hd m c⟩

end Desc.K14.Law
