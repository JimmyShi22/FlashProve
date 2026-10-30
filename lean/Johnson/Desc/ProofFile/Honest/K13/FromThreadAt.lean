-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/FromThreadAt.lean: kind K13, the members' batching: THE PREMISES
OF FromThread.lean (this folder) ON THE THREAD's PARAMETERS, AT THE LIBRARY's OWN PARAMETERS
(`FirstThread.lettersAt`, Honest/Thread/FirstAt.lean): the full size. Statements with their proofs:
two evaluations by Lean's kernel on the written lists, three unfoldings, and calls of the library's
laws under the hypothesis h under which these parameters are laid (`P5J.AtMgA`).
Main names:
  `m3_place`: number 355 of the written list of places is the kind's place.
  `m3_pile_open`: the item "pile" is open at the border number 355.
  `m3_pile_at`, `m3_pileOne_at`: at these parameters the two items say "all rows on the table are
    true" at the library's reader through the book of commitment trees.
  `m3_pinW_at`: at these parameters the item "pinW" holds of the thread's witness at every state.
  `k13_pinW_at`: so the share of `Exchange` at "pinW" holds at every border: by unfolding of these
    parameters; neither the thread nor the member's step is used.
  `k13_rows_full`: the full size's written number of rows is the plan's.
  `m3_member_place`: number 355 of the first chain's flat list stands at the kind's place.
  `m3_member_fields`: it has the kind's rounds and states no oracle message.
  `k13_memberIs_at`: `MemberIs` (ShapeAtM3.lean of this folder) holds of it: from a state without a
    mark of failure it returns wherever the kind's own sub-protocol does, and that one returns
    wherever it does.

What is not claimed. That the hypothesis h can be met. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt
import Johnson.Desc.ProofFile.Honest.K13.FromThread
import Johnson.Desc.ProofFile.Honest.K13.AtMember
import Johnson.Desc.ProofFile.Honest.K13.ShapeAtM3
import Johnson.Desc.ProofFile.Honest.K13.ExchangeOf
import Johnson.P5J.PlacesPaid
import Johnson.P5J.Cols13Paid
import Johnson.Desc.Sound.PlanAsk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Block Chain Strs)
open VerifiableInference.Desc.First (Item start blockPlaces)
open VerifiableInference.Desc.K13 (battRounds atM3 whereOf)
open VerifiableInference.Desc.K13.Law (RowsTrue rwBook)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt Script WtF)

set_option maxRecDepth 100000 in
/-- Number 355 of the written list of places is the kind's place. -/
theorem m3_place : P5J.At.ps[355]? = some ⟨1, none, 3, .K13⟩ := by decide +kernel

set_option maxRecDepth 100000 in
/-- The item "pile" is open at the border number 355. -/
theorem m3_pile_open :
    Item.pile ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 355 := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₁ Rc' Tr' X' : Type}
  (hs : List (Placed (Local W₁ Rc' ProofFile.Inst Tr') (Local W₁ Rc' ProofFile.Inst Tr') X'))
  (Q : Script Bk (Local W₁ Rc' ProofFile.Inst Tr') (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₁ Rc' ProofFile.Inst Tr' → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₁ Rc' ProofFile.Inst Tr' → Prop) (rides : Nat → Local W₁ Rc' ProofFile.Inst Tr' → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- At the library's own parameters the item "pile" says: all rows on the table are true, at the
library's reader. -/
theorem m3_pile_at (w : Local W₁ Rc' ProofFile.Inst Tr') (a : ProofFile.InstPub × TS) (y : Strs) (v : WtF) :
    ((lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Mg w).pile a y v ↔
      RowsTrue (rwBook h.𝔇.arr h.𝔇.mat13 a) a.2 v := Iff.rfl

/-- The like of the item "pileOne". -/
theorem m3_pileOne_at (w : Local W₁ Rc' ProofFile.Inst Tr') (a : ProofFile.InstPub × TS) (y : Strs) (v : WtF) :
    ((lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Mg w).pileOne a y v ↔
      RowsTrue (rwBook h.𝔇.arr h.𝔇.mat13 a) a.2 v := Iff.rfl

/-- At the library's own parameters the item "pinW" holds of the thread's witness, at every state,
all oracles and all challenges: there the decoder of the committed table is the constant "the cells
that the thread's witness has". -/
theorem m3_pinW_at (k : Coins Bk) (w : Local W₁ Rc' ProofFile.Inst Tr') (a : ProofFile.InstPub × TS) (y : Strs)
    (hd : List Fmt.Drawn) :
    Item.holds (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).N
      ((lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).mg w) Item.pinW a y
      (Q.wit k w hd) := rfl

/-- **The share at the item "pinW"**, at the library's own parameters, at every border: by unfolding
of these parameters: neither the thread in front nor the member's step is used. -/
theorem k13_pinW_at (b : Nat) :
    ExchangeOf (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread b
      [Item.pinW] := by
  intro blk hb k s m En ds y cols s' _ _ _ ds' i hi
  obtain rfl : i = Item.pinW := List.mem_singleton.1 hi
  exact m3_pinW_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps k _ _ _ _

include h in
/-- The full size's written number of rows is the plan's: by the library's test on the shape as read
back (`P5J.fullShape13`, Johnson/P5J/Cols13Paid.lean; `full_nums`, Johnson/Desc/Sound/PlanAsk.lean).
-/
theorem k13_rows_full : OnBytes.Flat.numsFull.rows = (whereOf Zp).lin.matrixRows :=
  congrArg (·.rows) (Desc.K14.Law.full_nums _ (P5J.fullShape13 h.scope h.laid))

include h in
/-- Number 355 of the first chain's flat list stands at the kind's place. -/
theorem m3_member_place {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[355]? = some blk) :
    blk.place = ⟨1, none, 3, .K13⟩ := by
  have e := P5J.At.places_paid h.scope h.reads h.laid
  have q : (blockPlaces cF.blocksInOrder)[355]? = some blk.place := by
    unfold blockPlaces
    rw [List.getElem?_map, hb]
    rfl
  rw [e, m3_place] at q
  exact (Option.some.inj q).symm

include h in
/-- It has the kind's rounds and states no oracle message. -/
theorem m3_member_fields {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[355]? = some blk) :
    blk.rounds = battRounds (whereOf Zp) ∧
      blk.oracles = List.replicate (2 + (whereOf Zp).lin.kCol) [] := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact k13_member_fields O (List.mem_of_getElem? hb) (m3_member_place h hb)

include h in
/-- At the library's own parameters `MemberIs` (ShapeAtM3.lean of this folder) holds: number 355 of
the first chain's flat list has the kind's rounds; from a state without a mark of failure it returns
wherever the kind's own sub-protocol does; and that one returns wherever it does. -/
theorem k13_memberIs_at : MemberIs cF.blocksInOrder 355 h.𝔇.P13 Unit := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact memberIs_open O fun _ hb => m3_member_place h hb

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.m3_place
#print axioms ProofFile.Honest.K13.m3_pile_open
#print axioms ProofFile.Honest.K13.m3_pile_at
#print axioms ProofFile.Honest.K13.m3_pileOne_at
#print axioms ProofFile.Honest.K13.m3_pinW_at
#print axioms ProofFile.Honest.K13.k13_pinW_at
#print axioms ProofFile.Honest.K13.k13_rows_full
#print axioms ProofFile.Honest.K13.m3_member_place
#print axioms ProofFile.Honest.K13.m3_member_fields
#print axioms ProofFile.Honest.K13.k13_memberIs_at
