--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/K6Tie.lean: **THE TIE AT ONE c, AS FAR AS THIS HOUSE CAN CARRY IT ALONE**:
Law/K6Cut.lean's assembly at one record (k06_ord) asked the lookup's item and the rider's item AT
K6's OWN READING OF THE CELLS (compCut w). HERE THEY MAY STAND AT ANY OTHER RECORD OF CELLS cL THAT
AGREES WITH IT INSIDE THE RANGES (Law/CellsAlike.lean: SameCells, at the seat's sizes): so another
file's law may end at its own reading (which
walks into the neighbour's matrix beyond a matrix's features, where ours is 0), and what is left of
the tie is ONE SENTENCE ON TWO READINGS, cell by cell, inside the ranges: STATED AND PROVED.
OBJECT: no constant of the seated text: a tool between our relation on cells and the landed
Hd.HeadOrdLB. USER: none yet; meant: whoever joins the lookups' law at the head (head_rows |
head_guests at its headCells) and K6's (k6OwnCut) at the table. LETTERS: cL: the other house's
record of cells: tied by SameAt alone; the rest are k06_ord's.
  SameAt W c c' · lookCallsAt_same · riderAt_same · **k06_ord_tie**
WHAT IT DOES NOT SAY. THAT ANY OTHER HOUSE's READING AGREES WITH compCut w INSIDE THE RANGES: the
lookups' cells are "the one integer below 2^18 whose cast the entry is" of ITS messages' entries at
the trunk's own places (its adrOf_* lemmas): that these messages are the table's witness's, and the
entries the casts of ownQ's integers (its MatsAre; the library's Base), is owed: not ours alone. All
that Law/K6Cut.lean's
k06_ord does not say. No chance in it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6Cut
import Johnson.Desc.Kinds.Law.CellsAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model.Verify (borderOf)
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.OnPublicFiles.Flat (GE Holds)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT)

/-- Two records of cells agree on what the head's relation names, at the seat's sizes. -/
def SameAt (W : OnBytes.Model.Verify.Public) (c c' : NCells) : Prop :=
  @SameCells (sizesOf W.hS) c c'

namespace Came

/-- The lookup's item, at the record's letters, reads no cell beyond the ranges. -/
theorem lookCallsAt_same (W : OnBytes.Model.Verify.Public) (tab : Nat → Nat) (s : S) (y : Nat)
    (c c' : NCells) (hon : K6On W s)
    (hy : Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y) (h : SameAt W c c')
    (hl : LookCallsAt W tab s y c) : LookCallsAt W tab s y c' := by
  obtain ⟨_, hplan, _, hreq, hyV, _⟩ := hon
  letI : Sizes := sizesOf W.hS
  letI : Policy := (parOf W.hS 0).policy
  letI : Request := requestOf s
  letI : Token := ⟨y⟩
  exact lookCalls_same h (planFacts (sT := W.hS.tabS) hplan) hreq (hyV y hy) _ tab hl

/-- The rider's item likewise. -/
theorem riderAt_same (W : OnBytes.Model.Verify.Public) (s : S) (y : Nat) (c c' : NCells)
    (hon : K6On W s) (h : SameAt W c c') (hr : RiderAt W s y c) : RiderAt W s y c' := by
  obtain ⟨_, hplan, _, _, _, _⟩ := hon
  letI : Sizes := sizesOf W.hS
  letI : Policy := (parOf W.hS (workOf W)).policy
  letI : Request := requestOf s
  letI : Token := ⟨y⟩
  exact rider_same h (planFacts (sT := W.hS.tabS) hplan) hr

/-- **THE ASSEMBLY AT ONE RECORD, WITH THE LOOKUP's AND THE RIDER's ITEMS AT ANOTHER READING OF THE
CELLS.** -/
theorem k06_ord_tie {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
    (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
    (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
    (pl : Nat → Nat × Bool × Nat × Nat) (hr0 : rows ≤ hRef) (hc0 : cols ≤ 2 ^ kRef) (s0 : S)
    (y : Nat) (x : Inst.Model.Instance Inst.Model.ppref) (i : Cm.Idx) (tab : Nat → Nat)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (cL : NCells) (hon : K6On Wp s0)
    (hin : K6In Wp s0 (compCut cs arr msR N s seat Wp pl w))
    (hy : Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat s0 = some y)
    (hsame : SameAt Wp cL (compCut cs arr msR N s seat Wp pl w).1)
    (hlook : LookCallsAt Wp tab s0 y cL) (hrider : RiderAt Wp s0 y cL)
    (hSm : OnBytes.Road.Hd.SmallH Wp.hS Wp.HLy (borderOf Wp.y) (P5J.ownQ cs arr msR N s seat w 24))
    (hF : OnBytes.Road.Hd.FullH Wp.hS) (hNum : OnBytes.Road.Hd.NumH Wp.hS Wp.HLy)
    (hBd : OnBytes.Road.Hd.BorderH (borderOf Wp.y)) (h8 : Wp.hS.digSh = 8) (hr : s0.rowR = x.r)
    (he : s0.rowE = x.e) (htok : ∀ t, t < 1024 → s0.tokv.getD t 0 = x.tok t) (hyx : y = x.y.val)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u) (hH : Holds w.cells i)
    (hy0 : x.e < Inst.Model.ppref.T → ((x.y.val : Nat) : ZMod Cb.Gl.p) = 0) :
    OnBytes.Road.Hd.HeadOrdLB Wp.hS Wp.HLy Wp.y (OnBytes.Road.Hd.npOf Wp.hS)
      (OnBytes.Road.Hd.polOf Wp.hS) i.mat x (P5J.ownQ cs arr msR N s seat w 24) :=
  k06_ord cs arr msR N s seat Wp pl hr0 hc0 s0 y x i tab w hon hin hy
    (lookCallsAt_same Wp tab s0 y cL _ hon hy hsame hlook) (riderAt_same Wp s0 y cL _ hon hsame
        hrider)
    hSm hF hNum hBd h8 hr he htok hyx htab hH hy0

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.lookCallsAt_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.riderAt_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k06_ord_tie
#check @VerifiableInference.Desc.Kinds.Head.Law.Came.k06_ord_tie
