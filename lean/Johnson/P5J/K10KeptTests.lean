-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10KeptTests.lean: TWO TESTS ON THE KEPT SEATS (`keptApartB`, `keptLowB`:
Johnson/Desc/First/Close/Law/PinKeptBack.lean) SAY YES AT THE CLOSED CONSTANT, AT EVERY PLACE OF THE
KIND K10: the premises T1 and T2 of K10's assembled law (`k10_two_cs`,
Johnson/Desc/First/Close/Law/LawTwoCs.lean). Statements and proofs; evaluations by the kernel.

  T1. `keptApart_full`: at the written numbers and the written seats' numbering, at every place of
    the kind K10 of `At.ps`: no kept seat has the number of a seat that the place lays: by the
    kernel. `keptApart_eq`: under the head the test at `At.arr Zp`, `At.N Zp cF` IS the test at the
    written values (`AtMg.N_six`, `AtMg.arr_is`). `k10_T1_at`: so it says yes.
  T2. `keptOpen_full`: behind every place of the kind K10 the item "pinKept" of its link is open: by
    the kernel, on the written lists. `k10_T2_at`: every kept tenant's tree lies below THE SEATED
    PIECE's OWN base: the table's test on the fence (`AtMg.fence`) at the border behind; the table's
    count of trees stays across the place (`k10_counts_at`); the piece's base is that count
    (`k10_base_at`).
  NEGATIVE LINES, by the kernel. `keptApart_next`: the kept seats of link l against the seats of
    group l + 1: A NUMBER IS SHARED at 24 of the 25 links (a kept message's number is its later
    copy's): T1 bears load. `keptLow_tight`: at base := the greatest kept tree the second test says
    no at all 24 links that keep something. `keptOpen_bent`: the next link's "pinKept" is open
    behind no such place.
  IDLE AT LINK 24: `kept_none_24`: nothing is kept there: both tests say yes of nothing.
    `kept_some`: at each of the links 0 to 23 something is kept.
Limits. The full size alone. Under the head. Nothing on soundness.

-/
import Johnson.P5J.K10Two
import Johnson.P5J.K10Open
import Johnson.Desc.First.Close.Law.PinKeptBack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start Item openSets sampledIn laysSeats
  fenceFit_at)
open VerifiableInference.Desc.First.Close (keptApartB keptLowB)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

set_option quotPrecheck false in
/-- The first chain's pieces' type. -/
local notation "PC" => Piece (ckP .two) FR (ProofFile.InstPub × TS) ProofFile.Cl
  (Wit (CellsM numsFull) At.Tok MsgT)

set_option quotPrecheck false in
/-- Its statements' type. -/
local notation "ST" => (ProofFile.InstPub × TS) × (Frame.E FR).Str

/-- The first test along the places of the kind K10, at the written values. -/
def keptApartW : Bool :=
  At.ps.all fun a => a.kind != KindName.K10 ||
    keptApartB (P5T.arrOf P5T.seatsAllFull) P5T.N0Full fullLinks a

theorem keptApart_full : keptApartW = true := by decide +kernel

/-- A negative line: against the next group's seats a number is shared at 24 of the 25 links. -/
theorem keptApart_next :
    ((List.range 25).filter fun l => (P5T.N0Full.keptOf l).all fun t =>
      (P5T.N0Full.group (l + 1)).all fun u =>
        P5T.arrOf P5T.seatsAllFull t.1 t.2 != P5T.arrOf P5T.seatsAllFull u.1 u.2) = [24] := by
  decide +kernel

/-- Nothing is kept at link 24: there both tests are idle. -/
theorem kept_none_24 : P5T.N0Full.keptOf 24 = [] := by decide +kernel

theorem kept_some : ((List.range 24).all fun l => !(P5T.N0Full.keptOf l).isEmpty) = true := by
  decide +kernel

/-- A negative line: at the greatest kept tree the second test says no. -/
theorem keptLow_tight :
    ((List.range 24).all fun l =>
      !keptLowB P5T.N0Full l (((P5T.N0Full.keptOf l).map (·.1)).foldl max 0)) = true := by
  decide +kernel

/-- "pinKept" of link (the place's + d) is open behind the place. -/
def keptOpenBy (d : ℕ) : Bool :=
  (List.range At.ps.length).all fun i => (At.ps[i]?).all fun a =>
    a.kind != KindName.K10 || (oAt (i + 1)).contains (Item.pinKept (a.link.getD 0 + d))

theorem keptOpen_full : keptOpenBy 0 = true := by decide +kernel

/-- A negative line: the next link's is open behind no such place. -/
theorem keptOpen_bent :
    ((List.range At.ps.length).any fun i => (At.ps[i]?).any fun a =>
      a.kind == KindName.K10 && (oAt (i + 1)).contains (Item.pinKept (a.link.getD 0 + 1))) =
      false := by decide +kernel

/-- Under the head the first test is the test at the written values. -/
theorem keptApart_eq (h : AtMg o Z D r Zp Np cF) (a : Place) :
    keptApartB (At.arr Zp) (At.N Zp cF) fullLinks a =
      keptApartB (P5T.arrOf P5T.seatsAllFull) P5T.N0Full fullLinks a := by
  obtain ⟨e1, e2, -⟩ := h.N_six
  unfold keptApartB laysSeats Numbers.group
  rw [e1, e2, h.arr_is]

/-- **T1 AT THE CONSTANT.** -/
theorem k10_T1_at (h : AtMg o Z D r Zp Np cF) (i : ℕ) (a : Place) (ha : At.ps[i]? = some a)
    (hk : a.kind = KindName.K10) : keptApartB (At.arr Zp) (At.N Zp cF) fullLinks a = true := by
  rw [keptApart_eq h a]
  have h1 := List.all_eq_true.1 keptApart_full a (List.mem_of_getElem? ha)
  rw [hk] at h1
  exact h1

/-- **T2 AT THE CONSTANT, AT THE SEATED PIECE's OWN BASE.** -/
theorem k10_T2_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (i : ℕ) (a : Place)
    (ha : At.ps[i]? = some a) (hk : a.kind = KindName.K10) (q : PC)
    (hq : (h.toAtMg.row L)[i]? = some q) :
    keptLowB (At.N Zp cF) (a.link.getD 0) q.base = true := by
  have hi : i < At.ps.length := (List.getElem?_eq_some_iff.1 ha).1
  have ho := List.all_eq_true.1 keptOpen_full i (List.mem_range.2 hi)
  rw [ha] at ho
  have ho' : (a.kind != KindName.K10 ||
      (oAt (i + 1)).contains (Item.pinKept (a.link.getD 0 + 0))) = true := ho
  rw [hk] at ho'
  have hm : Item.pinKept (a.link.getD 0) ∈ oAt (i + 1) := List.contains_iff_mem.1 ho'
  rw [k10_base_at h L q1 q2 q3 i a ha hk q hq, ← (k10_counts_at h i a ha hk).1]
  unfold keptLowB
  refine List.all_eq_true.2 fun t ht => decide_eq_true ?_
  exact fenceFit_at _ _ _ h.toAtMg.fence (i + 1) hi t (List.mem_flatMap.2 ⟨_, hm, ht⟩)

end P5J

#print axioms P5J.keptApart_full
#print axioms P5J.keptApart_next
#print axioms P5J.kept_none_24
#print axioms P5J.kept_some
#print axioms P5J.keptLow_tight
#print axioms P5J.keptOpen_full
#print axioms P5J.keptOpen_bent
#print axioms P5J.keptApart_eq
#print axioms P5J.k10_T1_at
#print axioms P5J.k10_T2_at
