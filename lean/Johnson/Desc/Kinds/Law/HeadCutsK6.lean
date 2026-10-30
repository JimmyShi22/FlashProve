-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadCutsK6.lean: THE NAMED PREMISE AT THE HEAD OF THE TABLE OF JOINTS' UPPER
STOREY (Johnson/P5J/MeansQ.lean: HeadCuts: "the head's four parts together give the head's half in
plain integers") AT A FILLING OF ITS LETTER headPart: A DEFINITION AND ITS LAWS.

  partsAtX, headPartK6   THE FILLING: the parts are the fields of the head's own record HeadParts
                   (Johnson/Desc/Kinds/HeadTablesLaw.lean), FREE OF THE CARRIED RECORD but for the
                   request: at the kind's letter Request made of the instance
                   x := (put (H.req a) (H.hid w).tok).val (Law/HeadPartsAtX.lean: reqX), the token
                   x.y, and the cells that Law/K6Cut.lean's compCut reads off the witness:
                     idn        Law/IdnPlain.lean's IdnPlain: idnSums and idnRows on the sizes, the
                                policy, the request and the cells alone
                     lookCalls  THE STORED TABLE HOLDS THE INDEX, AND HeadParts.lookCalls
                     rider      HeadParts.rider
                     small      Hd.SmallH at segment 24's own integers
                     lookCallsHeard   the part lookCalls AT THE REPLY THAT THE RECORD HAS HEARD (the
                                letter tokH) in the place of the witness's token
  PutKeeps, putReq_keeps   put turns the reply alone; putReq does.
  headPartK6_at    what the filling is at a part.
  THE STATEMENT's SIDE: headPartK6_blind: at ONE witness the filling is blind to the record but for
                   the request (and, at lookCallsHeard, the heard reply), and to the strings.
  THE WITNESS's SIDE: partsAtX_side, headPartK6_side: idn, rider and small read of the witness the
                   cells' two tables of integers (small: segment 24's own integers) alone: NOT ITS
                   TOKEN, NOT ITS STORED TABLE; of the instance no reply; no index. callsPart_congr:
                   lookCalls reads the stored table and the record of cells. comp_tok: the cells
                   read no token. (In the riding frame's own form: Law/ReadsOkK6.lean.)
  heard_is_calls, heard_to_calls   ONE SENTENCE, TWO TOKENS: at one record and witness; at two.
  FROM THE KIND's ITEMS AT A RECORD: idnPart_of_front (K6In; the two positions are the instance's)
  ·
                   callsPart_of_at (LookCallsAt) · riderPart_of_at (RiderAt): the last two where
                   requestOf s = reqX x: BY REWRITING.
  headOrd_of_parts the four parts give Hd.HeadOrdLB at segment 24's own integers.
  lastOf_mgOf      the stream that hidOf takes is the stream of segment 22's own list.
  headCuts_k6      MAIN: HeadCuts pp put (hidAtSeat ...) (headPartK6 ...).

WHY "the stored table holds the index" STANDS IN A PART, AND IN lookCalls. HeadCuts speaks of every
index i and has no premise that ties i to the witness; the head's half in plain integers is at i's
own output matrix. The table's list of what an item reads (First/Borders.lean: Item.reads) books the
witness's cells at constr m lookCalls and lookCallsHeard ("the keys read the weights"); at the
head's
idn, rider and small it books their tenants' messages and pads, NO CELLS AND NO TOKEN: so it stands
in lookCalls. The table's letter constr hands a
part
out only at an index that the decoded table holds: so whoever closes the part has that in hand.

WHAT IT IS NOT. IMPLICATIONS. PREMISES OF headCuts_k6: the files are in the goals' scope, are read,
and the public record is theirs · the tests on the plan · tab is the library's EX on 16 bits · rows
and cols within the reference's · hWord: THE 24TH EQUATION (Johnson/Goal/Meaning/HidHead.lean:
HeadWord) at every witness: paid in Law/HeadCutsWords.lean from another file's law, under public
conditions. THAT ANY BLOCK CLOSES A PART AT THIS FILLING IS NOT SAID: the closers owe "the record is
the instance's": requestOf s = reqX x; AND, FOR THE KEYS, THE TOKEN: x.y is the token that put lays:
at putReq, where e < T and the token is not 0, put leaves the request as it is: there
"the
heard token is x.y" is FALSE, and a closer needs "where e < T the keys read no token": typed by
nobody. The part small alone is light (true of every witness whose unpacked integers are small by
the
make): the weight is the table's own clause base, which constr adds beside it. The full size alone:
the numeral 24. No chance in it. Nothing on soundness by itself.
LETTERS. No letter stands under "there is". tab, tokH, put: public letters.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6Cut
import Johnson.Desc.Kinds.Law.HeadPartsAtX
import Johnson.Goal.Meaning.HeadOrdPlain
import Johnson.Goal.Meaning.HidHead
import Johnson.P5J.MeansQ
import Johnson.P5J.CellQ

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
open Inst.Model.All (Agree)
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.OnPublicFiles.Flat (GE Holds)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT SeatsNamed GroupsSeated)
open Norm (lt ls d lPd S2 T)
open Inst.Model Inst.Model.All in
/-- The library's congruence of the head's half in its stream, under this file's names. -/
theorem saysHead_stream {pp : ScalesAndPolicy} {i : Cm.Idx} {x : Instance ppref} {X1 X2 : Nat → Inst.Model.Vec}
    (h : Agree ppref X1 X2) (H : Meaning.HeadPlain pp i x X1) : Meaning.HeadPlain pp i x X2 :=
  Meaning.SaysHead.congr h (fun _ _ _ => rfl) H

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- **THE HEAD's FOUR PARTS, FREE OF THE CARRIED RECORD**: at an instance x and a witness w. -/
def partsAtX (tab : Nat → Nat) (i : Cm.Idx) (x : Instance ppref)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) : P5J.TPart → Prop :=
  letI : Sizes := sizesOf Wp.hS
  letI : Policy := (parOf Wp.hS (workOf Wp)).policy
  letI : Request := reqX x
  letI : Token := ⟨x.y.val⟩
  fun
  | .idn => IdnPlain (sizesOf Wp.hS) (parOf Wp.hS (workOf Wp)).policy (reqX x)
      (compCut cs arr msR N s seat Wp pl w).1
  | .lookCalls => Holds w.cells i ∧
      ∀ call, call < 6 → ∀ col, col < 2 ^ lJ (parOf Wp.hS 0).floor (callKeys call) →
      ∀ t, t < T → InTable tab call (keyTable (compCut cs arr msR N s seat Wp pl w).1 call col t)
  | .rider => ∀ t, t < T →
      clipAt (compCut cs arr msR N s seat Wp pl w).1.toCells (corner 0 t) = 0 ∧
        tableAt (compCut cs arr msR N s seat Wp pl w).1.toCells (corner 0 t) = 0
  | .small => OnBytes.Road.Hd.SmallH Wp.hS Wp.HLy (borderOf Wp.y)
      (P5J.ownQ cs arr msR N s seat w 24)
  | _ => True

/-- **THE FILLING OF THE TABLE's LETTER headPart.** tokH: the reply that the record has heard, as a
token: read by the part lookCallsHeard alone, which is the part lookCalls with that token in the
place of the witness's. -/
def headPartK6 {P : Type} (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
    (tokH : P × P5J.TS → Fin ppref.V) :
    P5J.TPart → Cm.Idx → P × P5J.TS → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop :=
  fun p i a _ w =>
    match p with
    | .lookCallsHeard =>
      partsAtX cs arr msR N s seat Wp pl tab i (put (H.req a) (tokH a)).val w .lookCalls
    | p => partsAtX cs arr msR N s seat Wp pl tab i (put (H.req a) (H.hid w).tok).val w p

/-- put turns the reply alone: it leaves the prompt and the two positions. -/
def PutKeeps (put : P5J.TReq → Fin ppref.V → P5J.TReq) : Prop :=
  ∀ q t, (put q t).val.prompt = q.val.prompt ∧ (put q t).val.r = q.val.r ∧
    (put q t).val.e = q.val.e

namespace Came

/-- putReq turns the reply alone. -/
theorem putReq_keeps : PutKeeps OnBytes.Flat.putReq := by
  intro q t
  unfold OnBytes.Flat.putReq
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- At a part other than lookCallsHeard the filling is partsAtX at the witness's token. -/
theorem headPartK6_at {P : Type} (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
    (tokH : P × P5J.TS → Fin ppref.V) (p : P5J.TPart) (hp : p ≠ .lookCallsHeard) (i : Cm.Idx)
    (a : P × P5J.TS) (y : Strs) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) :
    headPartK6 cs arr msR N s seat Wp pl tab put H tokH p i a y w =
      partsAtX cs arr msR N s seat Wp pl tab i (put (H.req a) (H.hid w).tok).val w p := by
  cases p <;> first | rfl | exact absurd rfl hp

/-- **ONE SENTENCE, TWO TOKENS**: where the reply that the record has heard is the witness's token,
the part lookCallsHeard is the part lookCalls. -/
theorem heard_is_calls {P : Type} (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
    (tokH : P × P5J.TS → Fin ppref.V) (i : Cm.Idx) (a : P × P5J.TS) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (h : tokH a = (H.hid w).tok) :
    headPartK6 cs arr msR N s seat Wp pl tab put H tokH .lookCallsHeard i a y w =
      headPartK6 cs arr msR N s seat Wp pl tab put H tokH .lookCalls i a y w := by
  show partsAtX cs arr msR N s seat Wp pl tab i (put (H.req a) (tokH a)).val w .lookCalls =
    partsAtX cs arr msR N s seat Wp pl tab i (put (H.req a) (H.hid w).tok).val w .lookCalls
  rw [h]

/-- **THE FILLING IS BLIND TO THE RECORD BUT FOR THE REQUEST** (and, at lookCallsHeard, the heard
reply): so a part rides past every block that leaves these; the strings are read by no part. -/
theorem headPartK6_blind {P : Type} (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
    (tokH : P × P5J.TS → Fin ppref.V) (p : P5J.TPart) (i : Cm.Idx) (a b : P × P5J.TS)
    (y y' : Strs) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hr : H.req b = H.req a)
    (ht : p = .lookCallsHeard → tokH b = tokH a) :
    headPartK6 cs arr msR N s seat Wp pl tab put H tokH p i b y' w =
      headPartK6 cs arr msR N s seat Wp pl tab put H tokH p i a y w := by
  by_cases hp : p = .lookCallsHeard
  · subst hp
    show partsAtX cs arr msR N s seat Wp pl tab i (put (H.req b) (tokH b)).val w .lookCalls =
      partsAtX cs arr msR N s seat Wp pl tab i (put (H.req a) (tokH a)).val w .lookCalls
    rw [hr, ht rfl]
  · rw [headPartK6_at cs arr msR N s seat Wp pl tab put H tokH p hp,
      headPartK6_at cs arr msR N s seat Wp pl tab put H tokH p hp, hr]

/-- **THE PART idn, FROM WHAT THE HEAD's LAW CLOSES IN FRONT** (Law/RowPins.lean: K6In), at a record
whose two positions are the instance's. -/
theorem idnPart_of_front (tab : Nat → Nat) (i : Cm.Idx) (x : Instance ppref)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (s0 : S) (hr : s0.rowR = x.r)
    (he : s0.rowE = x.e) (hin : K6In Wp s0 (compCut cs arr msR N s seat Wp pl w)) :
    partsAtX cs arr msR N s seat Wp pl tab i x w .idn :=
  idn_atX Wp.hS (readsOf Wp) (workOf Wp) s0 x _ hr he hin.1

/-- **THE PART lookCalls, FROM THE KIND's ITEM AT A RECORD** (Law/ReplyPins.lean: LookCallsAt)
whose
request is the instance's, at the instance's reply, and an index that the stored table holds: BY
REWRITING. -/
theorem callsPart_of_at (tab : Nat → Nat) (i : Cm.Idx) (x : Instance ppref)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (s0 : S) (hq : requestOf s0 = reqX x)
    (hH : Holds w.cells i)
    (hl : LookCallsAt Wp tab s0 x.y.val (compCut cs arr msR N s seat Wp pl w).1) :
    partsAtX cs arr msR N s seat Wp pl tab i x w .lookCalls := by
  unfold LookCallsAt at hl
  rw [hq] at hl
  exact ⟨hH, hl⟩

/-- **THE PART rider, FROM THE KIND's ITEM AT A RECORD** (Law/K06Means.lean: RiderAt) whose request
is the instance's, at any token. -/
theorem riderPart_of_at (tab : Nat → Nat) (i : Cm.Idx) (x : Instance ppref)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (s0 : S) (y : Nat)
    (hplan : (parOf Wp.hS (workOf Wp)).ok = true) (hq : requestOf s0 = reqX x)
    (hl : RiderAt Wp s0 y (compCut cs arr msR N s seat Wp pl w).1) :
    partsAtX cs arr msR N s seat Wp pl tab i x w .rider := by
  unfold RiderAt CornerGuests at hl
  rw [hq] at hl
  exact @rider_any_token (sizesOf Wp.hS) (parOf Wp.hS (workOf Wp)).policy (reqX x) Wp.hS.tabS y
    x.y.val hplan _ _ rfl hl

/-- **THE WITNESS's SIDE: idn, rider AND small READ OF THE WITNESS THE CELLS' TWO TABLES OF INTEGERS
AND SEGMENT 24's OWN INTEGERS ALONE, OF THE INSTANCE ITS PROMPT AND TWO POSITIONS ALONE, AND NO
INDEX**: not the witness's token, not the stored table, not the reply. -/
theorem partsAtX_side (tab : Nat → Nat) (i i' : Cm.Idx) (x x' : Instance ppref)
    (w w' : Wit (Fin rows → Fin cols → GE) Tok MsgT) (p : P5J.TPart)
    (hplan : (parOf Wp.hS (workOf Wp)).ok = true) (hp : x.prompt = x'.prompt) (hr : x.r = x'.r)
    (he : x.e = x'.e)
    (h1 : (compCut cs arr msR N s seat Wp pl w).1.cell =
      (compCut cs arr msR N s seat Wp pl w').1.cell)
    (h2 : (compCut cs arr msR N s seat Wp pl w).1.stream =
      (compCut cs arr msR N s seat Wp pl w').1.stream)
    (h3 : p = .small → P5J.ownQ cs arr msR N s seat w 24 = P5J.ownQ cs arr msR N s seat w' 24)
    (hpp : p = .idn ∨ p = .rider ∨ p = .small)
    (h : partsAtX cs arr msR N s seat Wp pl tab i x w p) :
    partsAtX cs arr msR N s seat Wp pl tab i' x' w' p := by
  have hq := reqX_congr x x' hp hr he
  rcases hpp with rfl | rfl | rfl
  · show IdnPlain _ _ (reqX x') _
    rw [← hq]
    exact idnPlain_wh _ _ _ _ _ h1 h2 h
  · have h' : (letI : Sizes := sizesOf Wp.hS
        letI : Policy := (parOf Wp.hS (workOf Wp)).policy
        letI : Request := reqX x'
        letI : Token := ⟨x.y.val⟩
        ∀ t, t < T →
          clipAt (compCut cs arr msR N s seat Wp pl w).1.toCells (corner 0 t) = 0 ∧
            tableAt (compCut cs arr msR N s seat Wp pl w).1.toCells (corner 0 t) = 0) := by
      rw [← hq]
      exact h
    exact @rider_any_token (sizesOf Wp.hS) (parOf Wp.hS (workOf Wp)).policy (reqX x') Wp.hS.tabS
      x.y.val x'.y.val hplan _ _ h1 h'
  · show OnBytes.Road.Hd.SmallH _ _ _ (P5J.ownQ cs arr msR N s seat w' 24)
    rw [← h3 rfl]
    exact h

/-- The part lookCalls reads of the witness its stored table and the record of cells alone. -/
theorem callsPart_congr (tab : Nat → Nat) (i : Cm.Idx) (x : Instance ppref)
    (w w' : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hc : w.cells = w'.cells)
    (hcomp : (compCut cs arr msR N s seat Wp pl w).1 = (compCut cs arr msR N s seat Wp pl w').1) :
    partsAtX cs arr msR N s seat Wp pl tab i x w .lookCalls =
      partsAtX cs arr msR N s seat Wp pl tab i x w' .lookCalls := by
  unfold partsAtX
  simp only [hc, hcomp]

/-- The cells and segment 24's own integers read no token of the witness. -/
theorem comp_tok (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (t : Tok) :
    compCut cs arr msR N s seat Wp pl { w with tok := t } = compCut cs arr msR N s seat Wp pl w ∧
      P5J.ownQ cs arr msR N s seat { w with tok := t } = P5J.ownQ cs arr msR N s seat w :=
  ⟨rfl, rfl⟩

/-- **THE WITNESS's SIDE AT THE FILLING**: at idn, rider and small: from one witness to another with
the same cells' two tables and the same integers of segment 24: whatever their tokens and stored
tables; at any two indices; where put turns the reply alone. -/
theorem headPartK6_side {P : Type} (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
    (tokH : P × P5J.TS → Fin ppref.V) (hK : PutKeeps put)
    (hplan : (parOf Wp.hS (workOf Wp)).ok = true) (i i' : Cm.Idx) (a : P × P5J.TS) (y y' : Strs)
    (w w' : Wit (Fin rows → Fin cols → GE) Tok MsgT) (p : P5J.TPart)
    (h1 : (compCut cs arr msR N s seat Wp pl w).1.cell =
      (compCut cs arr msR N s seat Wp pl w').1.cell)
    (h2 : (compCut cs arr msR N s seat Wp pl w).1.stream =
      (compCut cs arr msR N s seat Wp pl w').1.stream)
    (h3 : p = .small → P5J.ownQ cs arr msR N s seat w 24 = P5J.ownQ cs arr msR N s seat w' 24)
    (hpp : p = .idn ∨ p = .rider ∨ p = .small)
    (h : headPartK6 cs arr msR N s seat Wp pl tab put H tokH p i a y w) :
    headPartK6 cs arr msR N s seat Wp pl tab put H tokH p i' a y' w' := by
  have hne : p ≠ .lookCallsHeard := by
    rcases hpp with rfl | rfl | rfl <;> decide
  rw [headPartK6_at cs arr msR N s seat Wp pl tab put H tokH p hne] at h ⊢
  obtain ⟨k1, k2, k3⟩ := hK (H.req a) (H.hid w).tok
  obtain ⟨k1', k2', k3'⟩ := hK (H.req a) (H.hid w').tok
  exact partsAtX_side cs arr msR N s seat Wp pl tab i i' _ _ w w' p hplan (k1.trans k1'.symm)
    (k2.trans k2'.symm) (k3.trans k3'.symm) h1 h2 h3 hpp h

/-- **ONE SENTENCE, TWO TOKENS, AT TWO RECORDS AND TWO WITNESSES**: the part lookCallsHeard at (b,
w)
is the part lookCalls at (a, w'), where w' has w's stored table and cells, the request is the same,
and w' hides the reply that b has heard. -/
theorem heard_to_calls {P : Type} (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
    (tokH : P × P5J.TS → Fin ppref.V) (i : Cm.Idx) (a b : P × P5J.TS) (y y' : Strs)
    (w w' : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hr : H.req b = H.req a)
    (ht : (H.hid w').tok = tokH b) (hc : w'.cells = w.cells)
    (hcomp : compCut cs arr msR N s seat Wp pl w' = compCut cs arr msR N s seat Wp pl w) :
    headPartK6 cs arr msR N s seat Wp pl tab put H tokH .lookCallsHeard i b y' w =
      headPartK6 cs arr msR N s seat Wp pl tab put H tokH .lookCalls i a y w' := by
  show partsAtX cs arr msR N s seat Wp pl tab i (put (H.req b) (tokH b)).val w .lookCalls =
    partsAtX cs arr msR N s seat Wp pl tab i (put (H.req a) (H.hid w').tok).val w' .lookCalls
  rw [hr, ht]
  unfold partsAtX
  simp only [hc, hcomp]

/-- **THE FOUR PARTS GIVE HeadOrdLB AT SEGMENT 24's OWN INTEGERS.** -/
theorem headOrd_of_parts (hr0 : rows ≤ hRef) (hc0 : cols ≤ 2 ^ kRef) (tab : Nat → Nat)
    (i : Cm.Idx) (x : Instance ppref) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hF : OnBytes.Road.Hd.FullH Wp.hS) (hNum : OnBytes.Road.Hd.NumH Wp.hS Wp.HLy)
    (hBd : OnBytes.Road.Hd.BorderH (borderOf Wp.y)) (h8 : Wp.hS.digSh = 8)
    (hplan : (parOf Wp.hS (workOf Wp)).ok = true) (h3 : Inst.Model.Head3 x)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hp : ∀ p ∈ P5J.parts4, partsAtX cs arr msR N s seat Wp pl tab i x w p) :
    OnBytes.Road.Hd.HeadOrdLB Wp.hS Wp.HLy Wp.y (OnBytes.Road.Hd.npOf Wp.hS)
      (OnBytes.Road.Hd.polOf Wp.hS) i.mat x (P5J.ownQ cs arr msR N s seat w 24) := by
  have hidn := hp .idn (by decide)
  obtain ⟨hsum, hrows⟩ := @parts_of_plain (sizesOf Wp.hS) (parOf Wp.hS (workOf Wp)).policy (reqX x)
    ⟨x.y.val⟩ _ hidn
  obtain ⟨hH, hlook⟩ := hp .lookCalls (by decide)
  have hrider := hp .rider (by decide)
  have hSm : OnBytes.Road.Hd.SmallH Wp.hS Wp.HLy (borderOf Wp.y)
      (P5J.ownQ cs arr msR N s seat w 24) := hp .small (by decide)
  have hC : _root_.Policy.HeadCl (OnBytes.Road.Hd.npOf Wp.hS) (OnBytes.Road.Hd.polOf Wp.hS) i.mat x
      (OnBytes.Road.Hd.cellsH Wp.hS Wp.HLy (borderOf Wp.y) (ownCut cs arr msR N s seat Wp w)) :=
    headCl_atX Wp.hS (workOf Wp) x i.mat (parOf Wp.hS 0).floor tab
      (compCut cs arr msR N s seat Wp pl w).1 hF h8 hplan h3 htab (whOf_holds hr0 hc0 hH)
      (@HeadParts.mk (sizesOf Wp.hS) (parOf Wp.hS (workOf Wp)).policy (reqX x) ⟨x.y.val⟩ _ _ _
        hsum hrows hlook hrider
        (fun m f t => by cases m <;> exact cut_small hSm _ _ _)
        (fun f t => cut_small hSm _ _ _))
  refine Meaning.headOrd_congr hNum hBd (agreeH_cut _ _ _ _)
    ⟨Meaning.smallH_congr (agreeH_cut _ _ _ _).symm hSm, hC, fun he => ?_⟩
  rw [h3.2.2 he]
  rfl

/-- The stream that hidOf takes (group 11's list as hidOf makes it) is the stream of segment 22's
own list: lastOf reads number iXO alone, and the make leaves that number. -/
theorem lastOf_mgOf {X : OnBytes.Model.Verify.Public} (Nx : Meaning.XoNum X.y)
    (own : Nat → Mats Int) :
    Agree ppref (Meaning.lastOf X.y (Meaning.mgOf X.y own 11))
      (Meaning.lastOf X.y (own 22)) := by
  refine Meaning.lastOf_congr Nx fun r c => ?_
  unfold Meaning.mgOf
  rw [if_neg]
  intro hh
  have h1 : (OnBytes.Model.Layer.matIx X.y).iXO = (OnBytes.Model.Layer.matIx X.y).iXI := hh.1
  have h2 : X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 =
      X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 4 := h1
  omega

/-- **THE HEAD's FOUR PARTS TOGETHER GIVE THE HEAD's HALF IN PLAIN INTEGERS.** -/
theorem headCuts_k6 {P : Type} {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : publicOf Z.pol Z.KL lay = .ok Wp) (hr0 : rows ≤ hRef) (hc0 : cols ≤ 2 ^ kRef)
    (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq) (tokV : Tok → Fin ppref.V)
    (req : P × P5J.TS → P5J.TReq)
    (dec : P × P5J.TS → Strs → Option (Fin rows → Fin cols → GE))
    (hSN : SeatsNamed arr N s seat) (hGS : GroupsSeated msR N) (tokH : P × P5J.TS → Fin ppref.V)
    (hplan : (parOf Wp.hS (workOf Wp)).ok = true)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hWord : ∀ w : Wit (Fin rows → Fin cols → GE) Tok MsgT,
      Meaning.HeadWord Wp (P5J.ownQ cs arr msR N s seat w)) :
    P5J.HeadCuts pp put (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS)
      (headPartK6 cs arr msR N s seat Wp pl tab put
        (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS) tokH) := by
  intro i a y w hp0
  have hp : ∀ p ∈ P5J.parts4, partsAtX cs arr msR N s seat Wp pl tab i
      (put (req a) (tokV w.tok)).val w p := by
    intro p hp4
    have h1 := hp0 p hp4
    rw [headPartK6_at cs arr msR N s seat Wp pl tab put _ tokH p (by
      intro e
      subst e
      revert hp4
      decide)] at h1
    exact h1
  have A := OnBytes.Road.Hd.core_of_scope hZ hR hX
  have B := (OnBytes.Road.Hd.eleven_of_core hX A (OnBytes.Road.Hd.npOf Wp.hS)).1
  have Bd := OnBytes.Road.Hd.borderH_of_layout B.lay B.switches B.sized B.sized2
  have NH := OnBytes.Road.Hd.numH_of_layout B.full B.head
  have Nx := Meaning.xoNum_of_core hX A
  have h3 := Meaning.head3_of_req (put (req a) (tokV w.tok))
  have O := headOrd_of_parts cs arr msR N s seat Wp pl hr0 hc0 tab i _ w B.full NH Bd B.sh hplan h3
    htab hp
  have H1 := Meaning.headPlain_of_ord hZ hR hX i _ _ h3 O
  have H2 := Meaning.headPlain_of_copy Nx (hWord w)
    (saysHead_stream (fun pos hpz j hj =>
      (Meaning.lastIn_head hX A (P5J.ownQ cs arr msR N s seat w 24) pos hpz j hj).symm) H1)
  exact saysHead_stream (fun pos hpz j hj =>
    (lastOf_mgOf Nx (P5J.ownQ cs arr msR N s seat w) pos hpz j hj).symm) H2

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.heard_is_calls
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headPartK6_blind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.idnPart_of_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headOrd_of_parts
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.lastOf_mgOf
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headCuts_k6
