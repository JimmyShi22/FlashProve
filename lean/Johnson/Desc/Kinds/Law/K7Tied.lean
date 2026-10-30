-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7Tied.lean.
IN THE SECOND FORM OF THE CHAIN OF PROMISES (Desc/Sound/TiedR.lean: TiedByR): a letter
Rch stands beside the table's promise at the border in front (meant: "this state is reached from the
first by the sub-protocols in front"): THE BILL's FIELDS rides AND frames MAY SPEND IT; k7_own ends
in Own at onR, k7_tiedBy in TiedByR (Desc/Sound/TiedSeatR.lean: tiedByR_of_own).

WORDS BELOW: "block": a sub-protocol · "the record": the verifier's state
· "a description": the IOP as written in Lean.
WHAT IT DOES NOT SHOW. No soundness. A RULE OVER LETTERS: NO MEMBER: no piece of any description is
shown to meet the bill. THE BILL K7Due IS PAID BY NOBODY HERE; its fields, by name, and whose each
is:
  constr  the meaning's field constr is constrQAt at this filling of headPart
            (at the table's files' composed meaning: their own lemma, by definition).
  rides   THE PROMISE RIDES over the block (the first half of the block's own law at the table): the
            table's files' rule for a quiet row carries it, clause by clause; of these clauses this
            library has the one on the record's shape (Law/ReplyShape.lean) and what the record
            behind is (Law/ReplyRest.lean); the rest is typed by nobody at this place.
  ext     the piece's extractor turns the witness's token to tokOf of the record behind, and nothing
            else (at the table's own extractor: Law/K7Calls.lean: ext_k7).
  ins, outs, ctx   the table's row at the block's number is the next token's (a test on the table).
  req, dec   the reading of the request, and the decoded table, are the same at the two records.
  tok     the token that the reading of the witness finds in the laid witness is the token that the
            record behind has heard (tokH).
  frames  what rides past the block rides (framesOfSides gives it from four
            premises: an item reads the witness through the components that the table names for it
            [at the head's five items over this filling, AT THE NUMBER 24, at the reading
            P5J.hidAtSeat, under its own premises on put and the plan: Law/ReadsOkK6.lean:
            readsOk_k6; at the other items: their fillers'] · no rider reads what the row lays
            [tests on the table] · the piece's extractor is the table's · the statement's side at
            one witness [at the head's items: Law/HeadCutsK6.lean: headPartK6_blind]): NOT JOINED
            HERE.
  mark, decodes   a mark in front stays a mark; "the stored table decodes" rides.
LETTERS. No "there is". get: what was handed to the chain and the carried record, in the chain's
record. hd: the head's segment's number. Mg: the meaning: the proofs here open its field constr
alone, by the bill's first field; all else of it is read by the bill's other fields.
OBJECT. A piece q at number k of the first chain's row, and the table's words at that number
(Desc/Sound/BordersQ.lean: onQ, insQ, outsQ, meansQ), AT ANY MEANING Mg WHOSE FIELD constr IS
P5J.constrQAt with the letter headPart filled by Law/HeadCutsK6.lean's headPartK6 (the bill's first
field).
USER. The next token's kind's share of the chain of promises (Desc/Sound/TiedPlaces.lean: KindTied),
through the carriage for a row whose extractor lays (Desc/Sound/TiedLays.lean: tiedBy_of_seatE).
WHAT IT IS. THE TIE OF THE NEXT TOKEN's BLOCK AT THE TABLE's OWN WORDS, FROM A NAMED BILL. PROVED
HERE, NOT ASKED: THE SECOND HALF OF THE BLOCK's OWN LAW: every witness of what the row opens behind
gives, by the extractor, a witness of what it closes in front.
  K7Due             the bill.
  k7_rel            the second half, at the row's two items ("constr hd lookCalls"; "no mark").
  k7_own            the block's own law at the table: no challenge is bad: by the rule for a
                    piece that meets its goal at every transcript (Desc/ChainEndGoodIn.lean:
                    goodIn_of_sure).
  k7_tiedBy         the tie (Desc/Sound/TiedSeat.lean: tiedBy_of_own, which is general in the
                    extractor).
THE MEANING IS A LETTER, not P5J.meaningQAt over a letter
for the other fields: the table's files' composed meaning has a layer more outside that one, which
leaves constr.

-/
import Mathlib
import Johnson.Desc.ChainEndGoodIn
import Johnson.Desc.Sound.TiedLays
import Johnson.Desc.Sound.TiedSeatR
import Johnson.Desc.Kinds.Law.K7Calls

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open Inst.Model (ppref)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs Place)
open VerifiableInference.Desc.First (S Numbers ModelPart Item Meaning start)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)
open OnBytes.Maker (uLT)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)
  {A Cl P : Type} {C : CK} {Fr : Frame} (hd : Nat) (tab : Nat → Nat)
  (put : P5J.TReq → Fin ppref.V → P5J.TReq)
  (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
  (tokH : P × S → Fin ppref.V) (tokOf : P × S → Tok)
  (digitsPart : Nat → P × S → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (links : List ModelPart) (ps : List Place)
  (get : A → P × S) (Rch : Nat → A × Fr.E.Str → Prop) (k : Nat)
  (q : Piece C Fr A Cl (Wit (Fin rows → Fin cols → GE) Tok MsgT))

/-- **THE BILL.** Rch: a condition beside the table's promise (the second form of the chain of
promises): "rides" and "frames" may spend it. -/
structure K7Due : Prop where
  constr : Mg.constr =
    P5J.constrQAt hd put H (headPartK6 cs arr msR N s seat Wp pl tab put H tokH) digitsPart
  rides : ∀ a τ b, onQ N Mg links ps get k a → Rch k a → q.ior.red.out a τ = some b →
    onQ N Mg links ps get (k + 1) b
  ext : ∀ a τ b w, q.ior.red.out a τ = some b →
    q.ext a τ w = ⟨w.cells, tokOf (get b.1), w.msg, w.pad⟩
  ins : (rowQ links ps k).ins = [.constr hd .lookCalls]
  outs : (rowQ links ps k).outs = [.constr hd .lookCallsHeard]
  ctx : (rowQ links ps k).ctx = []
  req : ∀ a τ b, q.ior.red.out a τ = some b → H.req (get b.1) = H.req (get a.1)
  dec : ∀ a τ b, q.ior.red.out a τ = some b →
    H.dec (get b.1) (strsOf Fr b.2) = H.dec (get a.1) (strsOf Fr a.2)
  tok : ∀ (b : P × S) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT),
    (H.hid ⟨w.cells, tokOf b, w.msg, w.pad⟩).tok = tokH b
  frames : q.Frames (onR N Mg links ps get Rch k) (onQ N Mg links ps get (k + 1))
    (meansQ N Mg get)
    (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k) (insQ links ps k)
  mark : ∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
    (get b.1).2.failed ≠ none
  decodes : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
    Mg.decodes (get b.1) (strsOf Fr b.2)

variable {cs arr msR N s seat Wp pl hd tab put H tokH tokOf digitsPart Mg links ps get Rch k q}

namespace Came

/-- **THE SECOND HALF OF THE BLOCK's OWN LAW.** -/
theorem k7_rel
    (D : K7Due cs arr msR N s seat Wp pl hd tab put H tokH tokOf digitsPart Mg links ps get Rch k
      q)
    (a : A × Fr.E.Str) (τ : Iop.Tr (uLT C q.ds)) (b : A × Fr.E.Str)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hb : q.ior.red.out a τ = some b)
    (hO : relAt (meansQ N Mg get) (outsQ links ps k) b w) :
    relAt (meansQ N Mg get) (insQ links ps k) a (q.ext a τ w) := by
  intro i hi
  unfold insQ at hi
  rw [D.ins, D.ctx] at hi
  simp only [List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · have h1 : Mg.constr hd .lookCallsHeard (get b.1) (strsOf Fr b.2) w :=
      hO (.constr hd .lookCallsHeard) (by
        unfold outsQ
        rw [D.outs]
        simp)
    rw [D.constr] at h1
    show Mg.constr hd .lookCalls (get a.1) (strsOf Fr a.2) (q.ext a τ w)
    rw [D.constr, D.ext a τ b w hb]
    exact k7_constr cs arr msR N s seat Wp pl hd tab put H tokH digitsPart (get a.1) (get b.1)
      (strsOf Fr a.2) (strsOf Fr b.2) w (tokOf (get b.1)) (D.req a τ b hb) (D.dec a τ b hb)
      (D.tok (get b.1) w) h1
  · have h2 : (get b.1).2.failed = none := hO .unmarked (by
      unfold outsQ
      simp)
    show (get a.1).2.failed = none
    by_contra h
    exact D.mark a τ b hb h h2

/-- **THE BLOCK's OWN LAW AT THE TABLE.** -/
theorem k7_own
    (D : K7Due cs arr msR N s seat Wp pl hd tab put H tokH tokOf digitsPart Mg links ps get Rch k
      q) :
    q.Own (onR N Mg links ps get Rch k) (onQ N Mg links ps get (k + 1)) (meansQ N Mg get)
      (insQ links ps k) (outsQ links ps k) :=
  goodIn_of_sure q _ _ _ _ fun a τ b ha hb =>
    ⟨D.rides a τ b ha.1 ha.2 hb, fun w hw => k7_rel D a τ b w hb hw⟩

/-- **THE TIE.** -/
theorem k7_tiedBy
    (D : K7Due cs arr msR N s seat Wp pl hd tab put H tokH tokOf digitsPart Mg links ps get Rch k
      q) :
    TiedByR N Mg links ps get Rch k q (onR N Mg links ps get Rch k)
      (onQ N Mg links ps get (k + 1)) (relAt (meansQ N Mg get) (insQ links ps k))
      (relAt (meansQ N Mg get) (outsQ links ps k)) :=
  tiedByR_of_own N _ links ps get Rch k q (k7_own D)
    (fun a τ b w i ha hr _ hb hon hall hi hin =>
      D.frames a τ b w i ⟨ha, hr⟩ hb hon hi hin (hall i (Or.inl ⟨hi, hin⟩)))
    D.mark D.decodes

end Came

end VerifiableInference.Desc.Kinds.Head.Law
