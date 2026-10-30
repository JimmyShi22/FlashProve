-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkHeadTie.lean: the tie before the first fold holds after the link's steps and the
batching.

OnBytes/Slice/BlkTies.lean writes down what ties the columns that a later block of the program reads
to the oracle messages that were sent (`GroupTie`). This file shows that a run of the link's steps
and of the batching reaches that tie: the batched row has no form on a kept member, the group's
layout has the two folded rows' oracle messages as its members, with their blocks at row 0 and at
row 2^a (the rows of one of them, filled up to a power of two), and these two and the fresh mask
make up one tree, in that order.

Main theorems.
 `linkMessage_numbers`, `linkMessage_shapes`   the numbers and the shapes of the link's three oracle
                    messages, written out.
 `LinkRan.bat_noKept`   the batched row has no form on a kept member.
 `LinkRan.bat_tie`      the tie, if the link's message is put in one tree.


Not claimed. Nothing for a link whose fresh mask is not sent with the folded rows.
-/
import OnBytes.Slice.BlkLinkSeatToy
import OnBytes.Slice.BlkNoKept
import OnBytes.Slice.BlkTies
import OnBytes.Slice.BlkTop

set_option autoImplicit false

namespace OnBytes.Slice

open Params (LinkShape)

/-- The numbers of the link's three oracle messages, written out. -/
theorem linkMessage_numbers (S : LinkShape) (hm : S.masksAhead = true) (n0 : Nat) :
    (List.range (linkMessage S 1).size).map (· + n0) = [n0, n0 + 1] ++ [n0 + 2] := by
  have hs : (linkMessage S 1).size = 3 := by simp [linkMessage, hm]
  rw [hs]
  simp [List.range_succ, Nat.add_comm]

/-- The shapes of the link's three oracle messages, written out. -/
theorem linkMessage_shapes (S : LinkShape) (hm : S.masksAhead = true) :
    (linkMessage S 1).toList.map (·.shape) = [rowShape S, rowShape S, maskShape S] := by
  unfold linkMessage
  rw [if_pos hm]
  rfl

/-- No member of the link's group is kept. -/
theorem linkLay_kept (S : LinkShape) (T : Statement) (i : Nat) :
    (linkLay S T).kept.getD i false = false := by
  show (#[false, false] : Array Bool).getD i false = false
  rcases i with _ | _ | i
  · rfl
  · rfl
  · simp

section
variable {S : LinkShape} {first further : TableKey} {c c1 c2 : Ctx} {x : LinkRun} {D : LinkData}
  (hR : LinkRan S first further c c1 x D)
  {G : Group} {L : GroupLayout} {θ : E} {row : GroupRow} (hB : BatRan x.group c1 c2 G L θ row)

include hR hB

/-- The row that the batching returns has no form on a kept member. -/
theorem LinkRan.bat_noKept : row.kept = #[] :=
  combine_noKept _ _ _ _ _ (hR.bat_input hB).2.2
    (linkBat_fits S c.st D.places _ _ D.rows0 D.rows1 D.rE (eqRow_target _ _ _ _ _ _ hR.eqRow).2
      (columnRows_kind _ _ _ _ _ _ _ _ hR.rows0) (columnRows_kind _ _ _ _ _ _ _ _ hR.rows1)
      fun r hr => hR.st ▸ hR.fits r hr)
    (linkLay_kept S c.st)

/-- The tie before the first fold, after the link's steps and the batching, if the fresh mask is
sent with the folded rows and the link's message is put in one tree sh. s: the stage. cf: a context
that differs from the one after the batching in kept values alone. -/
theorem LinkRan.bat_tie (hm : S.masksAhead = true) (s : Sg) (sh : TreeShape)
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

/-- A run on a view from the start of an entry's chain: the next tree has the number 0, the codes
are those of the parameter bytes, and the statement is the start's. -/
theorem start_entry (p : Params.Link) (V : Fmt.View) :
    (startCtx (Entry.start p) V).ch.firstTree + (startCtx (Entry.start p) V).ch.roots = 0 ∧
      (startCtx (Entry.start p) V).st.codes = p.codes ∧
      (startCtx (Entry.start p) V).st = (Entry.start p).st :=
  ⟨rfl, rfl, rfl⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.linkMessage_numbers
#print axioms OnBytes.Slice.linkMessage_shapes
#print axioms OnBytes.Slice.linkLay_kept
#print axioms OnBytes.Slice.LinkRan.bat_noKept
#print axioms OnBytes.Slice.LinkRan.bat_tie
#print axioms OnBytes.Slice.start_entry
