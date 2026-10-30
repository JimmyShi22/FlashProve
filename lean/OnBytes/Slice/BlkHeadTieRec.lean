-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkHeadTieRec.lean: the tie before the first fold holds after the link's steps and the
batching, from `LinkRanR`.

OnBytes/Slice/BlkLinkSeat.lean and BlkHeadTie.lean show, from `LinkRan`, that a run of
the link's steps and of the batching reaches the tie of OnBytes/Slice/BlkTies.lean (`GroupTie`): the
batched row has no form on a kept member, the group's layout has the two folded rows' oracle
messages as its members, and these two and the fresh mask make up one tree. None of this reads a
row's coefficients or target; `bat_noKept` asks that each row which the test takes in, the records'
rows among them, fits the statement (`LinkRanR.fitsSt`). This file says the three theorems again
from `LinkRanR` (OnBytes/Slice/BlkLinkRanRec.lean).

Main theorems.
 `LinkRanR.bat_seat`     where the link's oracle messages sit after the batching.
 `LinkRanR.bat_noKept`   the batched row has no form on a kept member.
 `LinkRanR.bat_tie`      the tie, if the link's message is put in one tree.
Not claimed. Nothing for a link whose fresh mask is not sent with the folded rows. No setting's
numbers.

-/
import OnBytes.Slice.BlkHeadTie
import OnBytes.Slice.BlkLinkHeadRec

set_option autoImplicit false

namespace OnBytes.Slice

open Params (LinkShape)

section
variable {S : LinkShape} {first further : TableKey} {c c1 c2 : Ctx} {x : LinkRun} {D : LinkDataR}
  (hR : LinkRanR S first further c c1 x D)
  {G : Group} {L : GroupLayout} {θ : E} {row : GroupRow} (hB : BatRan x.group c1 c2 G L θ row)

include hR hB

/-- Where the link's oracle messages sit, after the batching: they are the parts of one tree, if
the link's message is put in one tree sh. cf: a context that differs from the one after the
batching in kept values alone. -/
theorem LinkRanR.bat_seat (sh : TreeShape) (h1 : D.lay.shapes = #[sh])
    (ht : ∀ i, i < (linkMessage S 1).size → D.lay.tree.getD i 0 = 0 ∧ D.lay.part.getD i 0 = i)
    (hmain : sh.mainSymbols =
      (((linkMessage S 1).toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray)
    (hmask : sh.maskSymbols =
      (((linkMessage S 1).toList.map (·.shape)).map fun s => s.maskRows * 3).toArray)
    (cf : Ctx) (hn : Blk.SameButNotes c2 cf) :
    Seat cf ((List.range (linkMessage S 1).size).map (· + c.st.oracles.size))
      (c.ch.firstTree + c.ch.roots) sh.logN ((linkMessage S 1).toList.map (·.shape)) := by
  refine seat_of_sent c cf (linkMessage S 1) D.lay sh hR.placed ?_ (fun i => ?_) h1 ht hmain hmask
  · rw [hn.book]
    exact (hR.bat_keeps hB).2.1
  · rw [hn.st, hB.st, begun_shape, hR.st, linkStR, linkSt_shape]

/-- The row that the batching returns has no form on a kept member. -/
theorem LinkRanR.bat_noKept : row.kept = #[] :=
  combine_noKept _ _ _ _ _ (hR.bat_input hB).2.2
    (linkBat_fitsR S c.st D.places _ _ (D.rec0 ++ (D.rec1 ++ D.rows0)) D.rows1 D.rE D.rowsR
      hR.runRows_eq hR.fitsSt)
    (linkLay_kept S c.st)

/-- The tie before the first fold, after the link's steps and the batching, if the fresh mask is
sent with the folded rows and the link's message is put in one tree sh. s: the stage. cf: a context
that differs from the one after the batching in kept values alone. -/
theorem LinkRanR.bat_tie (hm : S.masksAhead = true) (s : Sg) (sh : TreeShape)
    (h1 : D.lay.shapes = #[sh])
    (ht : ∀ i, i < (linkMessage S 1).size → D.lay.tree.getD i 0 = 0 ∧ D.lay.part.getD i 0 = i)
    (hmain : sh.mainSymbols =
      (((linkMessage S 1).toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray)
    (hmask : sh.maskSymbols =
      (((linkMessage S 1).toList.map (·.shape)).map fun s => s.maskRows * 3).toArray)
    (ha : sh.logN = s.C.a) (cf : Ctx) (hn : Blk.SameButNotes c2 cf) :
    GroupTie s (c.ch.firstTree + c.ch.roots) [rowShape S, rowShape S, maskShape S]
      #[some 0, some (2 ^ ceilLog2 S.rows)] #[none, none] cf row L (c.st.oracles.size + 2) := by
  have hL : L = linkLay S c.st := (hR.bat_input hB).2.1
  have hseat := hR.bat_seat hB sh h1 ht hmain hmask cf hn
  rw [linkMessage_numbers S hm, linkMessage_shapes S hm, ha] at hseat
  refine ⟨hR.bat_noKept hB, [c.st.oracles.size, c.st.oracles.size + 1], ⟨?_, fun w _ => ?_, ?_, ?_⟩,
    hseat⟩
  · rw [hL]
    rfl
  · rw [hL]
    exact linkLay_kept S c.st w
  · rw [hL]
    rfl
  · rw [hL]
    rfl

end

end OnBytes.Slice
