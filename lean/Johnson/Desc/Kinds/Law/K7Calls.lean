-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7Calls.lean.
WHAT IT DOES NOT SHOW. No soundness. NOT THE TIE OF THE NEXT TOKEN's ROW: ITS HEART ALONE: of what a
block's own law at the table asks ("where the block says yes: the promise holds behind, and every
witness behind gives, by the extractor, a witness in front") this file has the second half, at the
row's one item, and nothing of the first. FOUR PREMISES ARE PAID BY NOBODY HERE: hr (the reading of
the request is the same at the two records) · hdec (so is the decoded table) · ht (the token that
the reading of the witness finds in the laid witness is the token that the record behind has heard:
tokH, and the witness's reading H.hid, are LETTERS) · that the place is the next token's and its row
lays (hk, hl). The item "no mark" of the row is not here.
LETTERS. No "there is".
OBJECT. The table's two items at the row of the next token's block (Desc/First/Borders.lean:
segRow): it closes "constr m lookCalls" and opens "constr m lookCallsHeard"; their meaning at the
head's segment (P5J/MeansQ.lean: constrQAt) with the letter headPart filled by Law/HeadCutsK6.lean's
headPartK6; and the table's extractor at that row (Desc/Sound/BordersFill.lean: extQ).
USER. The own law of the next token's block at the table.
WHAT IT IS. ONE SENTENCE, TWO TOKENS, ACROSS THE BLOCK: IF THE HEAD's CALLS' KEYS ARE ROWS OF THEIR
TABLES AT THE REPLY THAT THE RECORD BEHIND HAS HEARD, THEN THEY ARE SO AT THE WITNESS's TOKEN IN
FRONT, ONCE THE EXTRACTOR HAS LAID THE HEARD REPLY AS THAT TOKEN.
  ext_k7            at a place of the kind K7 whose row lays, the table's extractor turns the
                    witness's token and nothing else.
  k7_constr         the sentence, at the table's items' meaning: by Law/HeadCutsK6.lean's
                    heard_to_calls (the sentence at the filling of headPart: two records, two
                    witnesses) and comp_tok (the components that the output head's rule reads off
                    the witness do not read its token).



-/
import Mathlib
import Johnson.Desc.Kinds.Law.HeadCutsK6
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Road (Mats)
open OnBytes.Model.Verify (borderOf publicOf)
open Inst.Model (ppref Instance ScalesAndPolicy)
open VerifiableInference.OnPublicFiles.Flat (GE Holds)
open VerifiableInference.Desc (Strs Place KindName)
open VerifiableInference.Desc.First (S Numbers ModelPart)
open VerifiableInference.Desc.Sound (Mem MsgT)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

namespace Came

/-- **THE SENTENCE, AT THE TABLE's ITEMS' MEANING**, hd: the head's segment's number. -/
theorem k7_constr {P : Type} (hd : Nat) (tab : Nat → Nat)
    (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
    (tokH : P × P5J.TS → Fin ppref.V)
    (digitsPart : Nat → P × P5J.TS → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop)
    (a b : P × P5J.TS) (y y' : Strs) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (t : Tok)
    (hr : H.req b = H.req a) (hdec : H.dec b y' = H.dec a y)
    (ht : (H.hid ⟨w.cells, t, w.msg, w.pad⟩).tok = tokH b)
    (h : P5J.constrQAt hd put H (headPartK6 cs arr msR N s seat Wp pl tab put H tokH) digitsPart hd
      .lookCallsHeard b y' w) :
    P5J.constrQAt hd put H (headPartK6 cs arr msR N s seat Wp pl tab put H tokH) digitsPart hd
      .lookCalls a y ⟨w.cells, t, w.msg, w.pad⟩ := by
  unfold P5J.constrQAt at h ⊢
  rw [if_neg (by decide)] at h ⊢
  refine ⟨fun e => (by cases e), fun M i hM hH => ?_⟩
  have h2 := h.2 M i (hdec.trans hM) hH
  rw [if_pos rfl] at h2 ⊢
  exact Eq.mp (heard_to_calls cs arr msR N s seat Wp pl tab put H tokH i a b y y' w
    ⟨w.cells, t, w.msg, w.pad⟩ hr ht rfl (comp_tok cs arr msR N s seat Wp pl w t).1) h2

end Came

end VerifiableInference.Desc.Kinds.Head.Law

namespace VerifiableInference.Desc.Sound

open VerifiableInference.Desc (Strs Place KindName)
open VerifiableInference.Desc.First (Numbers ModelPart)

/-- **At a place of the kind K7 whose row lays, the table's extractor turns the witness's token and
nothing else.** -/
theorem ext_k7 (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi)
    (arr : Nat → Nat → Nat)
    (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (Nat → Option (Nat × List UInt64)) → P × First.S → Option Cells)
    (c₀ : Cells) (tokOf : P × First.S → Tok) (N : Numbers)
    (links : List ModelPart) (p : Place) (hk : p.kind = .K7) (hl : (First.rowOf links p).lays = true)
    (a b : P × First.S) (y : Strs) (w : Wit Cells Tok MsgT) :
    extQ cs G arr smp ms decT c₀ tokOf N links p a y (some b) w =
      ⟨w.cells, tokOf b, w.msg, w.pad⟩ := by
  have h1 : First.laysSeats N links p = [] := by
    unfold First.laysSeats
    rw [hl, hk]
    rfl
  have h2 : First.laysPads N links p = [] := by
    unfold First.laysPads
    rw [hl, hk]
    rfl
  have h3 : First.laysTok links p = true := by
    unfold First.laysTok
    rw [hl, hk]
    rfl
  unfold extQ extAt mineAt minePadAt
  rw [h1, h2, h3]
  simp

end VerifiableInference.Desc.Sound
