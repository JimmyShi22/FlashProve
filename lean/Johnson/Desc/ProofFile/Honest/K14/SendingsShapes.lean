-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsShapes.lean: ONE PUBLIC TEST, WITH CODE, MEANT TO ACCEPT
ONLY SHAPES AT WHICH THE TWO SENDINGS' PARTS (Honest/K14/Sendings.lean) LAY A COIN WHEREVER A COIN
IS DUE.

The parts' moves are total: they return a message at every shape. At a shape that does not fit they
lay, at a place where a coin is due, the vector's entry or 0, or one coin for two coefficients of a
fold's hiding polynomial, without a word. This test is meant to reject every such shape; that it
does is proved nowhere. It reads the codes and the shape alone. It is meant to be evaluated where
the parts are placed beside the chain's sub-protocols, and EVERY LAW ON A COIN OF THESE PARTS IS TO
TAKE IT AS A NAMED PREMISE.

  msgShapeFits    one message, by what it is laid of:
                  (1) the description's own test on a sent shape (Own.sentShapeFits): it has a row;
                      the numbers of the codes that its rows name lie in the arrays; the degree
                      named for its main rows is 1 or 3, also where it has none
                  (2) a sampled message's pads fit their row (K1's padFits)
                  (3) laid of a vector and coins: either no mask row, a main row, entries of the
                      extension field (else a pad has three entries an answer, and one is laid), no
                      more answers than the code's message length, and AT LEAST ONE ANSWER (main
                      rows that are not sampled are a masking word: every place of theirs is due a
                      coin, and the parts would lay the vector there); or mask rows alone
                  (4) a fold's fresh table of k variables in 2 ^ h rows: no sample, no main row,
                      2 ^ h mask rows, h ≤ k (else two coefficients are one coin), 1 ≤ k, and
                      the 2 k - h + 1 places that the packing uses lie inside the mask code's
                      message length
  sendShapeFits   a sending: (5) every code's message length is a power of two (a sample row counts
                  a pad's places by the next power of two, the parts by the length); (6) trees can
                  be laid for its messages; every message passes msgShapeFits
  vecShapeFits, carriersFit   (9) o_u and o_omega carry a vector: the first arm of (3); the first
                  mask and o_sp have no main row
  sendingsFit     **the test**: (7) "send o_u" has messages (it has none where masks are sent ahead
                  and the test on G_u has no stage); both sendings pass sendShapeFits; (9);
                  (8) o_sp has a free entry: the entry number 0 of its mask row, which "SPLIT"
                  spends, is no pad
  sendingsFit_toy   it accepts the small shape of Johnson/Desc/K14/Honest/Toy.lean: a kernel
                  evaluation
  The #guard commands: it rejects the small shape turned in one number: at (1) to (5), (8) and (9);
  each comment says which other clauses reject with the one that it names. At o_u and o_omega (3)
  never rejects without (9), whose clauses on these two are (3)'s first arm. (3)'s CLAUSE "no mask
  row" HAS NO TEST OF ITS OWN: the line that bends it is rejected by (1) too. (2) rejects alone at
  no line: at o_u and o_omega, under (5), it is (3)'s clause on the answers. (6) rejects at one
  line, with three others. No negative test is laid for (7).

What it does not test. That the number atPoint is that of "LIN point" among the chain's rounds, and
that this round stands in front of the sendings: the parts read the point off the challenges heard,
and an empty or a wrong point is met without a word; no coin's place hangs on it. That a challenge
holds the seeds' elements: the test on challenges of Honest/Frame.lean has it.
THAT MASKS ARE SENT AHEAD (LinShape.masksAhead): without them "send o_u" has the one message o_u;
(9)'s clause on the first mask then reads a default shape and is idle, and the test can accept.
THAT THE SHAPE SPLITS (LinShape.sharedSplitNeeded): without the split "send o_omega" has o_omega
alone; (9)'s clause on o_sp and (8) are then asked of a shape that is not sent, and the test can
accept. So its yes is meant to say that in what IS sent a coin lies wherever a coin is due; it is no
promise that the first mask or o_sp is there: a law on a coin of one of these two is to ask for it
beside, by name.
THAT THE LIBRARY's TEST ON THE LINEAR PART's SHAPE ACCEPTS (LinShape.ok, in OnBytes.linOk,
OnBytes/Iop/Lin.lean): in a row of the committed table the matrix's places lie in front of the index
committer's pads: rowsOf (Honest/K14/Parts.lean), whose rows the two parts are handed, is the
committed rows' text only there.
THAT THE VECTORS FIT: that the folded row's entries fit o_u's main rows, and the matrix's rows
o_omega's (vectorRoom): clauses of foldeqOk (OnBytes/Iop/Foldeq.lean) and of linOk, not of
LinShape.ok. The test accepts the small shape with one main row at o_u, where the folded row has 18
entries and the main row holds 15 (seen by evaluation; no #guard of this file has it): the vector is
not laid whole there.
Limits. Definitions with code and evaluations, at the small shape alone; no law. Nothing on a
verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Sendings
import Johnson.Desc.K14.Honest.Toy
import Johnson.Desc.Own.Sent
import Johnson.Desc.Own.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open VerifiableInference.Desc (K1.Msg.of)
open Desc.K14 (P14)

/-- One message, by what it is laid of. -/
def msgShapeFits (codes : Codes) (s : OracleShape) : MsgSort → Bool
  | .plain _ =>
    VerifiableInference.Desc.Own.sentShapeFits codes s &&
      (s.answers == 0 || (K1.Msg.of codes s).padFits) &&
      ((s.maskRows == 0 && decide (0 < s.mainRows) && s.mainDeg == 3 &&
          decide (s.answers ≤ (codes.base.getD s.code default).ell) && decide (1 ≤ s.answers)) ||
        (s.mainRows == 0 && decide (0 < s.maskRows)))
  | .fresh k h =>
    VerifiableInference.Desc.Own.sentShapeFits codes s &&
      s.answers == 0 && s.mainRows == 0 && s.maskRows == 2 ^ h && decide (h ≤ k) &&
      decide (1 ≤ k) && decide (2 * k - h + 1 ≤ (codes.mask.getD s.maskCode default).ell)

/-- A sending. -/
def sendShapeFits (J : SendJob) : Bool :=
  VerifiableInference.Desc.Own.lengthsFit J.Q.codes &&
    (VerifiableInference.Desc.Own.treesMade J.Q.codes J.Q.sent).isSome &&
    (List.range J.Q.sent.size).all fun k =>
      msgShapeFits J.Q.codes (J.Q.sent.getD k default).shape (J.sort k)

/-- The shape of a message that carries a vector. -/
def vecShapeFits (codes : Codes) (s : OracleShape) : Bool :=
  s.maskRows == 0 && decide (0 < s.mainRows) && s.mainDeg == 3 &&
    decide (s.answers ≤ (codes.base.getD s.code default).ell) && decide (1 ≤ s.answers)

/-- Which of the four messages carry a vector, and which are coins alone. -/
def carriersFit (codes : Codes) (S : LinShape) : Bool :=
  vecShapeFits codes S.fold.u && vecShapeFits codes S.omega &&
    (((Desc.K14.withU S).getD #[]).getD 1 default).shape.mainRows == 0 &&
    S.sharedSplit.mainRows == 0

/-- **The test on the shapes of the two sendings.** -/
def sendingsFit (Q : P14) : Bool :=
  (Desc.K14.withU Q.S).isSome && sendShapeFits (jobU ⟨Q, 0⟩) && sendShapeFits (jobOmega ⟨Q, 0⟩) &&
    carriersFit Q.codes Q.S &&
    decide (0 < Send.freeMaskEntries Q.S.sharedSplit.maskRows
      (Q.codes.mask.getD Q.S.sharedSplit.maskCode default).ell Q.S.sharedSplit.answers)

/-- It accepts the small shape. -/
theorem sendingsFit_toy : sendingsFit Desc.K14.Honest.Toy.P = true := by decide +kernel

/-! ## Negative tests: the small shape turned in one number -/

/-- The small plan with another shape, and with other codes. -/
def withShape (S : LinShape) : P14 := { Desc.K14.Honest.Toy.P with S := S }
@[inherit_doc withShape]
def withCodes (c : Codes) : P14 := { Desc.K14.Honest.Toy.P with codes := c }

#guard sendingsFit Desc.K14.Honest.Toy.P
/-- o_sp's shape at the small plan, with a field of the main rows that is neither of the two. -/
def spDegTwo : OracleShape := { Desc.K14.Honest.Toy.P.S.sharedSplit with mainDeg := 2 }

-- (1) ALONE: the message's test rejects spDegTwo; (1) rejects it; (2) and (3), evaluated at that
-- same shape, accept it
#guard !msgShapeFits Desc.K14.Honest.Toy.P.codes spDegTwo (.plain false) &&
  !VerifiableInference.Desc.Own.sentShapeFits Desc.K14.Honest.Toy.P.codes spDegTwo &&
  (spDegTwo.answers == 0 || (K1.Msg.of Desc.K14.Honest.Toy.P.codes spDegTwo).padFits) &&
  (spDegTwo.mainRows == 0 && decide (0 < spDegTwo.maskRows))
#guard !sendingsFit (withShape { Desc.K14.Honest.Toy.P.S with
  sharedSplit := { Desc.K14.Honest.Toy.P.S.sharedSplit with mainDeg := 2 } })
-- (1), and (3) and (9) with it: o_omega's code's number beyond the array
#guard !sendingsFit (withShape { Desc.K14.Honest.Toy.P.S with
  omega := { Desc.K14.Honest.Toy.P.S.omega with code := 99 } })
-- (1), and (8) with it: o_sp's mask code's number beyond the array
#guard !sendingsFit (withShape { Desc.K14.Honest.Toy.P.S with
  sharedSplit := { Desc.K14.Honest.Toy.P.S.sharedSplit with maskCode := 99 } })
-- (2), (3) and (9): more answers at o_omega than its row has places
#guard !sendingsFit (withShape { Desc.K14.Honest.Toy.P.S with
  omega := { Desc.K14.Honest.Toy.P.S.omega with answers := 99 } })
-- (3), and (9) with it: NO ANSWER AT o_omega: main rows that are not sampled
#guard !sendingsFit (withShape { Desc.K14.Honest.Toy.P.S with
  omega := { Desc.K14.Honest.Toy.P.S.omega with answers := 0 } })
#guard !vecShapeFits Desc.K14.Honest.Toy.P.codes
    { Desc.K14.Honest.Toy.P.S.omega with answers := 0 } &&
  !msgShapeFits Desc.K14.Honest.Toy.P.codes
    { Desc.K14.Honest.Toy.P.S.omega with answers := 0 } (.plain false)
-- (3), and (9) with it: o_omega's entries over the base field
#guard !sendingsFit (withShape { Desc.K14.Honest.Toy.P.S with
  omega := { Desc.K14.Honest.Toy.P.S.omega with mainDeg := 1 } })
-- (3), and (1) and (9) with it (the shape names no mask code): a mask row beside o_omega's main
-- rows
#guard !sendingsFit (withShape { Desc.K14.Honest.Toy.P.S with
  omega := { Desc.K14.Honest.Toy.P.S.omega with maskRows := 1 } })
-- (4) the fresh table's h above its k, and k = 0: on the message's test itself
#guard msgShapeFits Desc.K14.Honest.Toy.P.codes
  ((jobU ⟨Desc.K14.Honest.Toy.P, 0⟩).Q.sent.getD 1 default).shape
  ((jobU ⟨Desc.K14.Honest.Toy.P, 0⟩).sort 1)
#guard !msgShapeFits Desc.K14.Honest.Toy.P.codes
  { ((jobU ⟨Desc.K14.Honest.Toy.P, 0⟩).Q.sent.getD 1 default).shape with maskRows := 4 }
  (.fresh 1 2)
#guard !msgShapeFits Desc.K14.Honest.Toy.P.codes
  ((jobU ⟨Desc.K14.Honest.Toy.P, 0⟩).Q.sent.getD 1 default).shape (.fresh 0 0)
-- (4) more places than the mask code's message length
#guard !msgShapeFits Desc.K14.Honest.Toy.P.codes
  ((jobU ⟨Desc.K14.Honest.Toy.P, 0⟩).Q.sent.getD 1 default).shape (.fresh 99 0)
-- (5) a mask code's message length off a power of two
#guard !sendingsFit (withCodes { Desc.K14.Honest.Toy.P.codes with
  mask := Desc.K14.Honest.Toy.P.codes.mask.map fun z => { z with ell := z.ell + 1 } })
-- (9): a vector's shape at o_sp: as a message it passes; carriersFit rejects
#guard msgShapeFits Desc.K14.Honest.Toy.P.codes Desc.K14.Honest.Toy.P.S.omega (.plain false) &&
  !carriersFit Desc.K14.Honest.Toy.P.codes { Desc.K14.Honest.Toy.P.S with
    sharedSplit := Desc.K14.Honest.Toy.P.S.omega }
-- (9), and (1), (3) and (6) with it (the shape names no base code): a main row at o_sp
#guard !sendingsFit (withShape { Desc.K14.Honest.Toy.P.S with
  sharedSplit := { Desc.K14.Honest.Toy.P.S.sharedSplit with mainRows := 1 } })
-- (8) as many answers at o_sp as its row has places: no free entry
#guard !sendingsFit (withShape { Desc.K14.Honest.Toy.P.S with
  sharedSplit := { Desc.K14.Honest.Toy.P.S.sharedSplit with
    answers := (Desc.K14.Honest.Toy.P.codes.mask.getD
      Desc.K14.Honest.Toy.P.S.sharedSplit.maskCode default).ell } })

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.sendingsFit_toy
