-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7Sides.lean.
WHAT IT DOES NOT SHOW. No soundness. A RULE OVER LETTERS: it names no sub-protocol and no state.
FIVE PREMISES: hr, hdec: the reading of the request, and the decoded table, are the same at the two
statements · hK: put turns the reply alone · hplan: a test on the plan · hbase: the reading's
sentence "base" at the head's link does not read the witness's token. No example shows that they can
be met together.
WORDS. "The statement's side", "the witness's side": the two things that turn where an item rides
past a sub-protocol whose extractor changes the witness (Desc/Sound/BordersSides.lean).
LETTERS. No "there is". a, b: the public part with the verifier's state, in front and behind. t: any
token.
OBJECT. constrQAt at K6's files' filling headPartK6, at the head's link's own
number, at the parts idn, rider and small.
USER. Law/K7AtMgAll.lean: three of the eight items that ride past the next token's place.
WHAT IT IS. AT THE PARTS idn, rider AND small THE HEAD's SENTENCE RIDES PAST A SUB-PROTOCOL THAT
LAYS THE TOKEN: what it says behind at w it says in front at w with any token laid.
  k7_side_constr    by Law/HeadCutsK6.lean: headPartK6_blind (the statement's side) and
                    headPartK6_side (the witness's side; its three premises on what the witness's
                    cut reads hold by definition: that file's comp_tok says the like).
NEAREST RELATIVE: Law/K7Calls.lean: k7_constr: the like from lookCallsHeard to lookCalls.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K7Calls

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

/-- **The parts idn, rider and small ride past a sub-protocol that lays the token.** -/
theorem k7_side_constr {P : Type} (hd : Nat) (tab : Nat → Nat)
    (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
    (tokH : P × P5J.TS → Fin ppref.V)
    (digitsPart : Nat → P × P5J.TS → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop)
    (a b : P × P5J.TS) (y y' : Strs) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (t : Tok)
    (hr : H.req b = H.req a) (hdec : H.dec b y' = H.dec a y) (hK : PutKeeps put)
    (hplan : (parOf Wp.hS (workOf Wp)).ok = true)
    (hbase : H.base hd w → H.base hd ⟨w.cells, t, w.msg, w.pad⟩) (p : P5J.TPart)
    (hpp : p = .idn ∨ p = .rider ∨ p = .small)
    (h : P5J.constrQAt hd put H (headPartK6 cs arr msR N s seat Wp pl tab put H tokH) digitsPart hd
      p b y' w) :
    P5J.constrQAt hd put H (headPartK6 cs arr msR N s seat Wp pl tab put H tokH) digitsPart hd
      p a y ⟨w.cells, t, w.msg, w.pad⟩ := by
  have hne : p ≠ .lookDigits := by
    rcases hpp with rfl | rfl | rfl <;> decide
  have hnh : p ≠ .lookCallsHeard := by
    rcases hpp with rfl | rfl | rfl <;> decide
  unfold P5J.constrQAt at h ⊢
  rw [if_neg hne] at h ⊢
  refine ⟨fun e => hbase (h.1 e), fun M i hM hH => ?_⟩
  have h2 := h.2 M i (hdec.trans hM) hH
  rw [if_pos rfl] at h2 ⊢
  have h3 : headPartK6 cs arr msR N s seat Wp pl tab put H tokH p i a y w :=
    Eq.mp (headPartK6_blind cs arr msR N s seat Wp pl tab put H tokH p i a b y y' w hr
      fun e => absurd e hnh) h2
  exact headPartK6_side cs arr msR N s seat Wp pl tab put H tokH hK hplan i i a y y w
    ⟨w.cells, t, w.msg, w.pad⟩ p rfl rfl (fun _ => rfl) hpp h3

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k7_side_constr
