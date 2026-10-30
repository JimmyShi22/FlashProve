-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6FourthConstr.lean: THE OUTPUT HEAD's BLOCK IN THE CHAIN OF PROMISES: OF ITS
FOURTH TIE (what the kind's law closes in front gives what the table's row closes) THE ITEMS THAT
ARE "constr", at the table's letter constr filled by Johnson/P5J/MeansQ.lean's constrQAt with the
head's parts filled by Law/HeadCutsK6.lean's headPartK6. Statements and proofs.

The row of the head's own block closes: constr m idn · worth m 3 "planes" · worth m 3 "keys" ·
worth m 3 "rider"; in its ctx stand pin m 0 · pinW · constr m small.

  constr_idn_of_front   constr hd idn AT THE RECORD IN FRONT, from K6In there (Law/RowPins.lean)
                   and the tie of the table's reader of the request to the record's two positions.
  constr_idn_of_words   the same, where the record's request's words are the request file's of what
                   the table's reader of the request gives: the form of the promise's new clause.
  constr_head_rides    constr hd p (p not lookDigits) at one record and strings, from the same at
                   another record and other strings, where the request, the decoded table and (at
                   lookCallsHeard) the heard reply are the same: so constr hd small comes back from
                   behind the block, and constr hd idn, rider, small ride past a block: THE
                   STATEMENT's SIDE, at one witness.

WHAT IT IS NOT. Implications. NOT THE FOURTH TIE: the three items "worth" are not touched: the
table's letter worth has no filling known here. hreq ("the record is the
instance's": its two positions) and hw (the record's words are the request file's) are premises:
that the words which the promise's clause names are requestWordsOf of what the table's reader of
the request gives is on two fillings in other files. hput holds at putReq (Law/HeadCutsK6.lean:
putReq_keeps). Nothing on soundness.
LETTERS. No letter stands under "there is". hd: the head's segment: a letter of constrQAt; the parts
themselves bear the numeral 24.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.HeadCutsK6
import Johnson.Flat.TiesAtReq

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (ppref Instance)
open VerifiableInference.OnPublicFiles.Flat (GE Holds)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat) {P : Type} (tab : Nat → Nat)
  (put : P5J.TReq → Fin ppref.V → P5J.TReq)
  (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
  (tokH : P × P5J.TS → Fin ppref.V)
  (digitsPart : Nat → P × P5J.TS → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop)

/-- **constr hd idn AT THE RECORD IN FRONT OF THE HEAD's OWN BLOCK.** -/
theorem constr_idn_of_front (hd : Nat) (a : P × P5J.TS) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hin : K6In Wp a.2 (compCut cs arr msR N s seat Wp pl w))
    (hreq : a.2.rowR = (H.req a).val.r ∧ a.2.rowE = (H.req a).val.e) (hput : PutKeeps put) :
    P5J.constrQAt hd put H (headPartK6 cs arr msR N s seat Wp pl tab put H tokH) digitsPart hd .idn
      a y w := by
  unfold P5J.constrQAt
  rw [if_neg (by decide)]
  refine ⟨fun h => absurd h (by decide), fun M i hM hi => ?_⟩
  rw [if_pos rfl, headPartK6_at cs arr msR N s seat Wp pl tab put H tokH .idn (by decide)]
  exact idnPart_of_front cs arr msR N s seat Wp pl tab i _ w a.2
    (hreq.1.trans (hput _ _).2.1.symm) (hreq.2.trans (hput _ _).2.2.symm) hin

/-- **The same, from the promise's clause on the request's words**: the record's words are the
request file's of what the table's reader of the request gives (requestWordsOf). -/
theorem constr_idn_of_words (hd : Nat) (a : P × P5J.TS) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hin : K6In Wp a.2 (compCut cs arr msR N s seat Wp pl w))
    (hw : a.2.req = OnBytes.Flat.requestWordsOf (H.req a).val) (hput : PutKeeps put) :
    P5J.constrQAt hd put H (headPartK6 cs arr msR N s seat Wp pl tab put H tokH) digitsPart hd .idn
      a y w := by
  have e := requestOf_words a.2 (H.req a).val hw
  exact constr_idn_of_front cs arr msR N s seat Wp pl tab put H tokH digitsPart hd a y w hin
    ⟨congrArg (·.r) e, congrArg (·.e) e⟩ hput

/-- **A PART OF THE HEAD RIDES**: from a record b and strings y' to a record a and strings y. -/
theorem constr_head_rides (hd : Nat) (p : P5J.TPart) (hp : p ≠ .lookDigits) (a b : P × P5J.TS)
    (y y' : Strs) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hr : H.req b = H.req a)
    (hdec : H.dec b y' = H.dec a y) (ht : p = .lookCallsHeard → tokH b = tokH a)
    (h : P5J.constrQAt hd put H (headPartK6 cs arr msR N s seat Wp pl tab put H tokH) digitsPart hd
      p b y' w) :
    P5J.constrQAt hd put H (headPartK6 cs arr msR N s seat Wp pl tab put H tokH) digitsPart hd p
      a y w := by
  unfold P5J.constrQAt at h ⊢
  rw [if_neg hp] at h ⊢
  refine ⟨h.1, fun M i hM hi => ?_⟩
  have h2 := h.2 M i (hdec.trans hM) hi
  rw [if_pos rfl] at h2 ⊢
  rw [← headPartK6_blind cs arr msR N s seat Wp pl tab put H tokH p i a b y y' w hr ht]
  exact h2

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.constr_idn_of_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.constr_idn_of_words
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.constr_head_rides
