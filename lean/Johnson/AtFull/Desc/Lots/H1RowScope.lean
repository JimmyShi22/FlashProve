-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/H1RowScope.lean.
WHAT IT DOES NOT SHOW. No soundness. NO EXAMPLE OF THE HEAD IS SHOWN IN THIS FILE; two, at storedPublicFiles and
at zGap alone, are AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what
they are worth. A JOINING OF FOUR CALLS: NO NEW MATHEMATICS, AND IT PAYS NONE OF ITS FOUR PREMISES.
At the goals' stored full-size public files hS and hR are proved theorems (VerifierAndGoals.inScope_full,
Johnson/Goal/Files/ScopeExample.lean; the field "full" of VerifierAndGoals.filesRead,
Johnson/Goal/Files/FilesReadProof.lean); THAT THE PUBLIC PART IS RETURNED (hZ) AND THAT THE
SEGMENTS' RECORDS ARE RETURNED (hG) IS SHOWN THERE BY NO THEOREM. What a skeleton is blind to, and
what the closed facts against the written table count for: as the head of
Johnson/AtFull/Desc/Lots/H1Row.lean says.
WORDS, OBJECT. As in H1Row.lean: the lot with the one block at "H:1", the next token's place (K7).
LETTERS. No "there is". P: the three public files; pp: what the goals' reader returns of them; Z:
the proof file's public part; G: the segments' records for a request of zeros. lay IS A FREE LETTER:
the bytes that are handed to pubPlain as the layout: NOTHING HERE TIES THEM TO A FILE OF P. At the
second hash OnBytes.secondHashFunction alone. NO OPENING OF THE PROOF FILE, NO PIN, NO RETURN OF THE CHAIN IS
ASKED OR SPENT: hS is the goals' scope, a closed test on the three public files; hR their reading.
USER. The premise hk (one row a lot) of ProofFile.Sk.back_of_skel
(Johnson/Desc/ProofFile/Law/Skel/SkelEnd.lean): with this the row of this lot owes what every lot's
row owes, and nothing of its own.
WHAT IT IS. h1_row_scope: THE LOT's SKELETON IS THE WRITTEN ONE, FROM THE SCOPE, THE READING AND THE
TWO RETURNS. The two hypotheses by field of h1_row_at are paid by other files' proved laws, called,
under no second name: G.built.size = 25 is the first half of IM.ground_gets
(Johnson/IMR/PureJoin.lean); G.W.hS.V = 202048 is the field V of numbers_in_scope
(Johnson/Goal/Meaning/HeadCondScope.lean) at the public record G.W, which IM.ground_publicK says to
be what publicOf returns.
IT HAS NO TEST OF ITS OWN: a joining can fail with its premises alone. That the row itself can fail
is h1_row_iff and h1_small (H1Row.lean). hR follows from hS (IM.reads_of_scope,
Johnson/IMR/MemberOfGate.lean): it is kept as a binder, since the called laws take it and that
file's imports are heavy: a caller has it in one line.

-/
import Johnson.AtFull.Desc.Lots.H1Row
import Johnson.IMR.PureJoin
import Johnson.Goal.Meaning.HeadCondScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots
open ProofFile.Sk

/-- **THE ROW, FROM THE SCOPE, THE READING AND THE TWO RETURNS.** -/
theorem h1_row_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) : lotSk G h1Lot = h1LotSk 24 true := by
  have hb : G.built.size = 25 := (IM.ground_gets hS hR hZ hG).1
  have hv : G.W.hS.V = 202048 :=
    (VerifiableInference.Desc.Kinds.Head.Law.InScope.numbers_in_scope hS hR
      (IM.ground_publicK hZ hG)).V
  exact h1_row_at G hb (by omega)

end Johnson.AtFull.Lots

#print axioms Johnson.AtFull.Lots.h1_row_scope
