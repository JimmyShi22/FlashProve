-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopyTxt.lean: the kind "the code switch" (K2): THE TEXT OF A
KEPT COPY, OFF THE PAD: a main entry of the lot's text `switchMsgTxt` (Honest/K2/ScriptLots.lean) at
a kept copy, off the pad's places, is the entry of the kept member as the closing returned it:
`(Wl.kept i).main r j`. The like of Honest/K2/Law/MainTxt.lean's two ends, which stand at the
switch's own messages. Three statements with their proofs; no definition.

  `mainRows_kept`   `mainRows` at a kept copy: the middle arm
  `msgTxt_copy_e`   THE END, over the extension field
  `msgTxt_copy_f`   the like over the base field: the first coordinate

i: the kept member's number; the copy is message number 1 + i of the switch's sending (0 is the
carrying message). By: `rowsLaid_inv` (Honest/K2/Law/SenderOwn.lean) · `msgTxt_rows`, `laidMain_e`,
`laidMain_f` (MainTxt.lean): the two proofs go as `msgTxt_main_e`'s and `msgTxt_main_f`'s there,
with `mainRows_kept` in `mainRows_own`'s stead. That the list `padInMain` and the test `padB` are
one: `padInMain_iff_padB` (Honest/K2/Law/PadPlaces.lean), not called.

Limits. ONE LINK OF A LONGER CHAIN. It names what the closing returned, Wl: it does not say what
Wl's kept member is: NOT that it is the first sender's message: that wants what is kept in arrays
(`frozenLeft`: the next link is `frozen_kept`, Honest/K2/Law/ClaimFrozen.lean), the fold's end, and
the rows that the closing lays anew (`segmentLeft`, Honest/K2/Closing.lean): none of these is opened
here. TWO COUNTS MEET: hi counts by `p.sizes.kept.length`, as `mainRows` does; the lots tell a kept
copy by `p.sizes.target.kept.size` (`firstSender`, ScriptLots.lean): nothing here makes these two
numbers equal; `Sizes.serves` does: a join of this law with the lots has to bring that test. hH AND
hV ARE PREMISES: that the switch is handed its coins, and that its rows are laid. Of the sending's
own stretch c.1 the right side names nothing. Wl is what the closing returns at the place, the
filling at the input's public part, the readers at the input, what was heard, and the carried
stretches c.2.2: it hangs on all five. Main rows alone; sampled messages alone (ha); inside the rows
and the row's length (hr, hj). An equation at one run's coins: what is WRITTEN where. NO LOT IS
LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MainTxt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left mainRows Sizes)

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- `mainRows` at a kept copy. -/
theorem mainRows_kept (Z : Sizes) (W : Left) (own : Nat → Nat → Nat → Cb.Gl.E) {i : Nat}
    (hi : i < Z.kept.length) : mainRows Z W own (1 + i) = (W.kept i).main := by
  have h1 : ¬ ((1 + i == 0) = true) := by simp
  have h2 : 1 + i ≤ Z.kept.length := by omega
  have h3 : 1 + i - 1 = i := by omega
  simp only [mainRows, if_neg h1, if_pos h2, h3]

/-- **THE END, OVER THE EXTENSION FIELD.** i: the kept member's number. -/
theorem msgTxt_copy_e (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed ch p k = some c) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V)
    (hw : NoWord (switchSent p.sizes p.others)) {i : Nat} (hi : i < p.sizes.kept.length)
    (hn : 1 + i < (switchSent p.sizes p.others).size) {r j : Nat}
    (h3 : (((switchSent p.sizes p.others).getD (1 + i) default).shape.mainDeg == 3) = true)
    (hr : r < ((switchSent p.sizes p.others).getD (1 + i) default).shape.mainRows)
    (hj : j < (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell)
    (ha : ((switchSent p.sizes p.others).getD (1 + i) default).shape.answers ≠ 0)
    (hp : (r, j) ∉ padInMain (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell
      ((switchSent p.sizes p.others).getD (1 + i) default).shape) :
    ∃ Wl, closing p (D w.x) (readers w) (hd.take (hd.length - 0))
        (Stretch.carried p.carries c.2.2) = .ok Wl ∧
      switchMsgTxt ch D readers closing p (1 + i) k w hd false r j =
        some ((Wl.kept i).main r j) := by
  obtain ⟨Wl, hW, hR⟩ := rowsLaid_inv hV
  refine ⟨Wl, hW, ?_⟩
  rw [msgTxt_rows ch D readers closing p _ k w hd hH hV false r j]
  show some ((V (1 + i)).main (_ == 3) r j) = _
  unfold Johnson.Prover.Send.Rows.main
  rw [if_pos h3, laidMain_e hw hR hn h3 hr hj ha hp, mainRows_kept _ _ _ hi]

/-- The like over the base field. -/
theorem msgTxt_copy_f (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed ch p k = some c) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V)
    (hw : NoWord (switchSent p.sizes p.others)) {i : Nat} (hi : i < p.sizes.kept.length)
    (hn : 1 + i < (switchSent p.sizes p.others).size) {r j : Nat}
    (h3 : (((switchSent p.sizes p.others).getD (1 + i) default).shape.mainDeg == 3) = false)
    (hr : r < ((switchSent p.sizes p.others).getD (1 + i) default).shape.mainRows)
    (hj : j < (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell)
    (ha : ((switchSent p.sizes p.others).getD (1 + i) default).shape.answers ≠ 0)
    (hp : (r, j) ∉ padInMain (p.sizes.codes.base.getD
      ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell
      ((switchSent p.sizes p.others).getD (1 + i) default).shape) :
    ∃ Wl, closing p (D w.x) (readers w) (hd.take (hd.length - 0))
        (Stretch.carried p.carries c.2.2) = .ok Wl ∧
      switchMsgTxt ch D readers closing p (1 + i) k w hd false r j =
        some (algebraMap Cb.Gl.F Cb.Gl.E ((Wl.kept i).main r j).c0) := by
  obtain ⟨Wl, hW, hR⟩ := rowsLaid_inv hV
  refine ⟨Wl, hW, ?_⟩
  rw [msgTxt_rows ch D readers closing p _ k w hd hH hV false r j]
  show some ((V (1 + i)).main (_ == 3) r j) = _
  unfold Johnson.Prover.Send.Rows.main
  rw [if_neg (by rw [h3]; exact Bool.false_ne_true), laidMain_f hw hR hn h3 hr hj ha hp,
    mainRows_kept _ _ _ hi]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.mainRows_kept
#print axioms ProofFile.Honest.K2.Law.msgTxt_copy_e
#print axioms ProofFile.Honest.K2.Law.msgTxt_copy_f
