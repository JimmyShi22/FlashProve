-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsRead.lean: THE FOUR READERS OF A TUPLE OF MESSAGES THAT K4's VALUE AT THE
REFERENCE SIZES TAKES (`RefSeat`, Johnson/Road/K4/CloseRef.lean: raw, maskAt, matAt, idxAt), AS
READINGS OF THE PINNED PART `PinM` (Johnson/Road/K4/K4Pins.lean). Definitions, and small lemmas
that say what each reader finds at the pinned part of a witness. No draw, no count.

  `tupleOf cs l seat t`: a signature's tuple of typed messages, out of the pinned part: member i's
    entries are read off the table at the seat of i.
  `SitsIn l seat ms N m`: A CONDITION ON THE PLAN: each member i of the list l sits at a seat of
    `pinSeats`, and the member of ms that `memAt` finds there has i's shape. NOT ASKED: that l is
    the list of a sending of ms: the lists may be cut otherwise.
  `tupleOf_part`: under `SitsIn` the tuple out of a witness's pinned part is the witness's own
    (`msgsOf`, Johnson/Desc/Sound/MsgSig.lean).
  `PinPlan Cells`: THE LETTERS ON THE PLAN: what the caller of the lookup on a link's calls reads
    (D, rad, the link's number: Johnson/Desc/First/Look/K3CallerAtt.lean), the seats of its
    signature's members; the reader rc of the stored table's cells; where entry j of the index
    masks stands in their message's tables (posI).
  THE SIGNATURE: the oracle messages that stand sent when the shift of the link's lookup on the
    calls is drawn (`sigListCalls`: the kept ones, then the link's own of moment 0).
  `PinPlan.raw tl`, `PinPlan.mask`: BY THE TWO TERMS OF THE LOOKUP's CALLER's OWN READING, CALLED: a
    cell of a matrix is the one unpacking of the committed symbols (`cellValS` of `symAt`, at the
    smallness test's public parameters tl), a mask entry is read off the link's first message with a
    mask row (`valAt` at `seatCalls`); 0 where there is no such cell, and where the reading fails.
    `raw_msgAtt`, `mask_msgAtt`: they are `msgAtt` at `enCell` and, below its number of mask
    entries, at `enMask`.
  `PinPlan.mat`: rc of the cells; 0 where the tuple holds none.
  `PinPlan.idx N`: the entry, at the place that posI names, of the table at the seat N.index.
  `PinPlan.seat`: the `RefSeat` at the verifier's state with these four readers.
  `tuple_part`, `mat_part`, `idx_part`: at the pinned part of a witness w the readers read w's own
    messages and cells: the caller's tuple under `SitsIn`; an index mask under "`memAt` finds u at
    N.index, and the place lies inside u's ranges".

OBJECT: none of its own: readers. USER: Johnson/Road/K4/K4PinsOwn.lean [not in this library]
(`PinPlan.seat`) · Johnson/Road/K4/K4PinsLay.lean (`raw`, `mask`, `tuple_part`). LETTERS, filled by
nobody: every field of `PinPlan`; the numbers N, the smallness test's public parameters tl, the
layout, the bounds and the four numbers that
`PinPlan.seat` hands through.

Limits. K04_law IS NOT PROVED BY THIS. NOTHING TIES THE LETTERS TO A PLAN: `SitsIn` is a premise of
the lemmas; the test itself has run nowhere (WHO COULD PAY IT: a run on the plan: it compares seats
and shapes alone; it wants that the table's numbers count the kept messages that a link sends anew
among the tenants of its moment 0, AND THAT EVERY MESSAGE OF THE LIST HAS A SAMPLE: `sigListCalls`
takes every message of moment 0, the table's numbers book sampled tenants alone: one message without
a sample and `SitsIn` is false at that plan); that the link's number is the table's segment's, and
that posI names the place at which the programs lay entry j, has no lemma. WITHOUT `SitsIn` THE
READERS READ ZERO TABLES, OR TABLES CUT TO ANOTHER SHAPE's RANGES, IN SILENCE. `SitsIn` SHUTS THE
ZERO TABLES ALONE. THAT A CELL, A MASK ENTRY OR AN INDEX MASK IS READ AT ALL WANTS MORE, among it:
every address that the readers name has a seat that fits (`Seated`, K3CallerAtt.lean; evaluated
nowhere) · the smallness test's public parameters tl name an array for each of its matrices (`symAt`
reads `tl.gtTree.getD μ 0`: where the list is too short it reads ARRAY NUMBER 0: ANOTHER ARRAY, NOT
A ZERO) · the value's bounds cover tl's sizes · posI j lies inside the member's ranges · the mask
row is as long as the value's number of slots. AT A LINK THAT THE REQUEST HAS NOT, THE LIST IS EMPTY
AND `SitsIn` HOLDS FOR NOTHING. `SitsIn` DOES NOT PIN seatT: where two members of the list have one
shape their two seats can be exchanged and it still holds (so it is at the real plans, by a run of
plain twins of these tests: the kept copy and one of the link's own messages, at every layers' link
but the first): `SymsOne` (Johnson/Road/K4/K4PinsSym.lean), which goes by the message's number,
tells them apart.
`seatCalls`, `sigListCalls` and `symAt` are a second writing of the programs' maps
(K3CallerAtt.lean's Limits (2)); a cell is 0 where a column of symbols is the packing of nothing
small (its Limits (3)): AT THE TABLE THE GUARD OF THAT 0 IS THE ITEM constr m small, WHICH ITS
AUTHORS' FILLING STATES AT ANOTHER TERM (`symAt` of Johnson/Goal/Meaning/HidSeat.lean: by the
message's number), not at this `symAt` (through `seatCalls` over `sigListCalls`): that the two read
one entry is a fact on the plan, typed nowhere. `msgAtt` was written for an attention link; that the
caller at a layers' link reads a mask entry and a cell by the same two terms is typed in
Johnson/Road/K4/K4PinsLay.lean.
-/
import Johnson.Road.K4.K4Pins
import Johnson.Desc.First.Look.K3CallerAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Model (HTailF2)
open OnBytes.Model.Layer (Lay)
open OnBytes.Desc.First.K4 (seatS)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls msgAtt enCell enMask cellJ
  szOf symAt valAt finOf_some)
open Cb.Pv.Tail (cellValS)
open VerifiableInference.Desc.Sound (Mem MsgT msgsOf InMsg memTab numOf msgs_forth)

section
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)

/-- A signature's tuple of typed messages, out of the pinned part: by the members' seats. -/
def tupleOf {Cells : Type} (t : PinM Cells) : (sigOf cs l).Msg :=
  fun i j => match j with
    | .inl q => t.1 (seat i) false q.1.val q.2.val
    | .inr q => t.1 (seat i) true q.1.val q.2.val

/-- **A condition on the plan**: each member of the list sits at a seat of `pinSeats`, and the
member of ms that is found there has its shape. -/
def SitsIn (ms : List Mem) (N : Numbers) (m : ℕ) : Prop :=
  ∀ i : Fin l.length, seat i ∈ pinSeats N m ∧
    ∃ u, memAt ms (seat i) = some u ∧ (u.1.l.get u.2).1 = (l.get i).1

variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)

/-- Inside the ranges of the member that is found at a seat of `pinSeats`, the pinned part of a
witness is the witness's table of that member (the one accessor). -/
theorem partOf_in (w : Wit Cells Tok MsgT) {x : ℕ × ℕ} (hx : x ∈ pinSeats N m) {u : Mem}
    (hu : memAt ms x = some u) (mask : Bool) (row place : ℕ)
    (hin : InMsg cs (u.1.l.get u.2).1 mask row place) :
    (partOf cs arr ms N m w).1 x mask row place = memTab cs arr w u mask row place := by
  rw [partOf_at cs arr ms N m w hx hu]
  exact (msgs_forth cs u.1.l u.1.seat arr w u.2 mask row place hin).symm

/-- **Under `SitsIn` the tuple out of a witness's pinned part is the witness's own.** -/
theorem tupleOf_part (hs : SitsIn l seat ms N m) (w : Wit Cells Tok MsgT) :
    tupleOf cs l seat (partOf cs arr ms N m w) = msgsOf cs l seat arr w := by
  funext i j
  obtain ⟨hx, u, hu, hsh⟩ := hs i
  have hseat : u.1.seat u.2 = seat i := (memAt_some hu).2
  have key : ∀ mask row place, InMsg cs (l.get i).1 mask row place →
      (partOf cs arr ms N m w).1 (seat i) mask row place =
        w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 mask row place := by
    intro mask row place hin
    rw [partOf_in cs arr ms N m w hx hu mask row place (by rw [hsh]; exact hin)]
    unfold memTab numOf
    rw [hsh, hseat]
  rcases j with q | q
  · exact key false q.1.val q.2.val (by
      unfold InMsg
      rw [if_neg (by decide)]
      exact ⟨q.1.isLt, q.2.isLt⟩)
  · exact key true q.1.val q.2.val (by
      unfold InMsg
      rw [if_pos rfl]
      exact ⟨q.1.isLt, q.2.isLt⟩)

end

/-- **The letters on the plan.** -/
structure PinPlan (Cells : Type) where
  /-- what the caller of the lookup on the link's calls reads -/
  D : Sent
  rad : OnBytes.OracleShape → ℕ
  link : ℕ
  /-- the seats (tree, tenant) of that caller's signature's members -/
  seatT : Fin (sigListCalls D rad link).length → ℕ × ℕ
  /-- the stored table's cells as a matrix -/
  rc : Cells → ℕ → ℕ → Cb.Gl.E
  /-- where entry j of the index masks stands in their message: mask table?, row, place -/
  posI : ℕ → Bool × ℕ × ℕ

namespace PinPlan
variable {Cells : Type} (A : PinPlan Cells)

/-- The caller's signature's tuple, out of the pinned part. -/
def tuple (t : PinM Cells) : (sigOf A.D.codes (sigListCalls A.D A.rad A.link)).Msg :=
  tupleOf A.D.codes (sigListCalls A.D A.rad A.link) A.seatT t

/-- **The matrices**: the cells behind the committed symbols; 0 where the smallness test's public
  parameters
has no such cell. -/
def raw (tl : HTailF2) (t : PinM Cells) : Mats Cb.Gl.E := fun a r c =>
  ((cellJ (szOf tl) a r c).map (cellValS (symAt A.D.codes (sigListCalls A.D A.rad A.link)
    (seatCalls A.D A.link) tl (A.tuple t)))).getD 0

/-- **The own mask row**; 0 where the reading fails. -/
def mask (t : PinM Cells) (j : ℕ) : Cb.Gl.E :=
  (valAt A.D.codes (sigListCalls A.D A.rad A.link) (seatCalls A.D A.link) (A.tuple t)
    (.mask j)).getD 0

/-- **The committed matrix of weights.** -/
def mat (t : PinM Cells) (r c : ℕ) : Cb.Gl.E :=
  match t.2 with
  | some C => A.rc C r c
  | none => 0

/-- **The index-mask message**: at the table's own seat of it. -/
def idx (N : Numbers) (t : PinM Cells) (j : ℕ) : Cb.Gl.E :=
  t.1 N.index (A.posI j).1 (A.posI j).2.1 (A.posI j).2.2

/-- The matrices are the lookup's caller's own reading of a cell, at every number of mask entries.
-/
theorem raw_msgAtt (tl : HTailF2) (ns : ℕ) (t : PinM Cells) (a r c : ℕ) :
    A.raw tl t a r c =
      msgAtt A.D.codes (sigListCalls A.D A.rad A.link) (seatCalls A.D A.link) tl ns (A.tuple t)
        (enCell ns tl a r c) := by
  unfold raw enCell
  cases cellJ (szOf tl) a r c <;> rfl

/-- The mask row is the lookup's caller's own reading of a mask entry, below its number of them. -/
theorem mask_msgAtt (tl : HTailF2) (ns : ℕ) (t : PinM Cells) (j : ℕ) (hj : j < ns) :
    A.mask t j =
      msgAtt A.D.codes (sigListCalls A.D A.rad A.link) (seatCalls A.D A.link) tl ns (A.tuple t)
        (enMask ns tl j) := by
  unfold mask enMask
  rw [finOf_some hj]
  rfl

/-- **The letters of the value at the reference sizes**, at the verifier's state, with these
four readers. -/
def seat (N : Numbers) (tl : HTailF2) (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) :
    RefSeat (PinM Cells) S where
  y := y
  nM := nM
  nR := nR
  nC := nC
  raw := A.raw tl
  maskAt := A.mask
  matAt := A.mat
  idxAt := A.idx N
  L := seatS
  n0 := n0
  ns := ns
  nx := nx
  v7 := v7

variable {Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)

/-- **Under `SitsIn` the caller's tuple out of a witness's pinned part is the witness's own**: so,
where the reading finds a seat that fits, the matrices and the mask row are read off the witness's
own messages. -/
theorem tuple_part (hs : SitsIn (sigListCalls A.D A.rad A.link) A.seatT ms N m)
    (w : Wit Cells Tok MsgT) :
    A.tuple (partOf A.D.codes arr ms N m w) =
      msgsOf A.D.codes (sigListCalls A.D A.rad A.link) A.seatT arr w :=
  tupleOf_part A.D.codes _ A.seatT arr ms N m hs w

/-- The weights are read off the witness's cells. -/
theorem mat_part (cs : OnBytes.Codes) (w : Wit Cells Tok MsgT) :
    A.mat (partOf cs arr ms N m w) = A.rc w.cells := rfl

/-- An index mask is the entry of the witness's table of the member u that is found at the table's
seat of the index masks' message (the one accessor), if the place lies inside u's ranges. -/
theorem idx_part (cs : OnBytes.Codes) {u : Mem} (hu : memAt ms N.index = some u)
    (w : Wit Cells Tok MsgT) (j : ℕ)
    (hin : InMsg cs (u.1.l.get u.2).1 (A.posI j).1 (A.posI j).2.1 (A.posI j).2.2) :
    A.idx N (partOf cs arr ms N m w) j =
      memTab cs arr w u (A.posI j).1 (A.posI j).2.1 (A.posI j).2.2 :=
  partOf_in cs arr ms N m w (List.mem_append_right _ (List.mem_singleton.2 rfl)) hu _ _ _ hin

end PinPlan

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tupleOf_part
#print axioms OnBytes.Road.K4.PinPlan.raw_msgAtt
#print axioms OnBytes.Road.K4.PinPlan.mask_msgAtt
#print axioms OnBytes.Road.K4.PinPlan.tuple_part
#print axioms OnBytes.Road.K4.PinPlan.mat_part
#print axioms OnBytes.Road.K4.PinPlan.idx_part
