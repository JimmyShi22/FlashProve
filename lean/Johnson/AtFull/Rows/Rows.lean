-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/Rows.lean: rowsWB = true with no premise: the second reading's text returns at
its four written values (Johnson/LPFE1R/RowsAtWritten.lean: rowsWB := rowsW.toOption.isSome;
rowsW := rowsFrom (writtenMade.at Hung.none) (List.replicate 25 1) 13 armAtW). A joining and no
more: `rowsWB_of_rest` (Johnson/AtFull/Rows/JoinKey.lean), fed with twelve premises out of 38 files.
A law file; no running text imports it.
  `rowsWB_true`: rowsWB = true.

Whence the premises. 37 closed facts, each alone in its file, each by Lean's kernel
(`decide +kernel`: by evaluation in Lean's kernel alone; no compiled code of this library is
trusted): CLenA (three lengths) · CLenB and CKd (the two long chains have 48,293 and 18,852 written
rounds: two drops each) · CD00 to CD26 (the 27 pieces of «proof 0») · CK1, CK2, CE0, CQ1, CQ2 (the
five short chains whole) · CT0L and CT4L (the ends of the two light twins). And `tailL_cut`
(TailHome.lean: the tail, out of ten closed facts: CT0 to CT6,
and `p0B`, `p1B`, `p2B` of Sends/ProofFirst.lean and Sends/ProofLater.lean). «key 0» is paid inside
`rowsWB_of_rest`, by its 32 pieces (KeyPiecesA.lean to KeyPiecesD.lean) and one length (`lenK`,
KeyPiecesAll.lean). In all 80 closed facts.

Limits. A maker returns at written values, and no more. That these four values are what the planner
makes of any public files is not said. It is about `rowsFrom`, a law file's second text: not about
the running test, nor about `sendRowsOf` on files. Of what the rows hold nothing is said. The
comparison with the written rounds is `sameAll`'s (four of a round's fields). The tail was asked at
twins without the arms and without «key 0»'s lookups; these twins are no part of the protocol and
write other plans than the planner's; `rows_of_partsL` (Twin.lean) carries the answer to the real
chains. The written tables of places (`placesW`, `placesK3`) come of an evaluator's print: the
closed facts hold them, nothing trusts them. The closed facts are not put before Lean's
kernel in this file: they are imported as checked at their own compile. Nothing on soundness or on
hiding.
-/
import Johnson.AtFull.Rows.JoinKey
import Johnson.AtFull.Rows.CLenA
import Johnson.AtFull.Rows.CLenB
import Johnson.AtFull.Rows.CKd
import Johnson.AtFull.Rows.CD00
import Johnson.AtFull.Rows.CD01
import Johnson.AtFull.Rows.CD02
import Johnson.AtFull.Rows.CD03
import Johnson.AtFull.Rows.CD04
import Johnson.AtFull.Rows.CD05
import Johnson.AtFull.Rows.CD06
import Johnson.AtFull.Rows.CD07
import Johnson.AtFull.Rows.CD08
import Johnson.AtFull.Rows.CD09
import Johnson.AtFull.Rows.CD10
import Johnson.AtFull.Rows.CD11
import Johnson.AtFull.Rows.CD12
import Johnson.AtFull.Rows.CD13
import Johnson.AtFull.Rows.CD14
import Johnson.AtFull.Rows.CD15
import Johnson.AtFull.Rows.CD16
import Johnson.AtFull.Rows.CD17
import Johnson.AtFull.Rows.CD18
import Johnson.AtFull.Rows.CD19
import Johnson.AtFull.Rows.CD20
import Johnson.AtFull.Rows.CD21
import Johnson.AtFull.Rows.CD22
import Johnson.AtFull.Rows.CD23
import Johnson.AtFull.Rows.CD24
import Johnson.AtFull.Rows.CD25
import Johnson.AtFull.Rows.CD26
import Johnson.AtFull.Rows.CK1
import Johnson.AtFull.Rows.CK2
import Johnson.AtFull.Rows.CE0
import Johnson.AtFull.Rows.CQ1
import Johnson.AtFull.Rows.CQ2
import Johnson.AtFull.Rows.CT0L
import Johnson.AtFull.Rows.CT4L
import Johnson.AtFull.Rows.TailHome

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

/-- **The second reading's text returns at its four written values.** -/
theorem rowsWB_true : rowsWB = true :=
  rowsWB_of_rest lens_W drops_p0 drops_k0
    (all27 pieceD_00 pieceD_01 pieceD_02 pieceD_03 pieceD_04 pieceD_05 pieceD_06 pieceD_07
      pieceD_08 pieceD_09 pieceD_10 pieceD_11 pieceD_12 pieceD_13 pieceD_14 pieceD_15 pieceD_16
      pieceD_17 pieceD_18 pieceD_19 pieceD_20 pieceD_21 pieceD_22 pieceD_23 pieceD_24 pieceD_25
      pieceD_26)
    key1_whole key2_whole entry_whole proof1_whole proof2_whole twinL_key0 twinL_proof0 tailL_cut

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rowsWB_true
