-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/SeatIsAtTests.lean: **"THE RECORD's SEAT IS THE DESCRIPTION's" (SeatIs) AT EVERY MEMBER OF THE SHARED CHAIN's TWO PROXIMITY TESTS, FROM TWO BOOLS THAT THE RECORD CARRIES.** Statements; each
proof is a call of MembersLaid.lean (the record's side) and of ToldAtFile.lean (the plan's side).

SeatIs (FramesTie.lean) is what the tie of the two frames (hM | hZ) asks of the record; as reported, not shown here, it is "the word's seam's one unpaid premise on the record".
  seatIs_nine    at Seat.onGu's door, under seatX 9 and membX 9: D has two members; the 0-th is o_u (number 0), the 1-st o_sp (number sU + 1); each has SeatIs (fun z => lo + z) D.book m (lo + m.t) (its part) o
                 at what the description tells of the tree lo + m.t, and its part is that oracle's tenant of its own message.
  seatIs_ten     at Seat.onGomega's door, under seatX 10 and membX 10: o_omega (number sU) and o_sp.
lo := the number of trees that the first chain's blocks tell. WHO PAYS seatX | membX: the chain's first record has them; every block hands them on (Johnson/Desc/Sound/SeatsCarried.lean · MembersCarried.lean).
PREMISES ON THE PLAN: hG (what the description's shared chain's blocks tell is what K14's chainOf's tell: ONE EQUATION BETWEEN TWO LISTS) · withU P.S = some sentU · the two layouts (Own.treesMade, and as
layTrees for seatX) · a split · the masks ahead.
Limits. At the chain's own record St. NO MEMBER IS SHOWN. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Coin.MembersLaid
import Johnson.Desc.K12.Coin.ToldAtFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.First (Plain Seat1)
open _root_.Desc.K14 (St P14 chainOf withU withOmega)
open _root_.Desc.K14.Law.Fence (seatX membX)

section
variable {Xi : Type} (G : FileDescription Xi) (c : Model.Verify.Chains) (P : P14)
  (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
  (sentU : Array OracleNotice)
  (layU layO : TreeLay)
  (hG : oraclesOf G.shared.blocksInOrder = oraclesOf (chainOf c P tests last).blocksInOrder)
  (hU : withU P.S = some sentU) (hlU : Own.treesMade P.codes sentU = some layU)
  (hlO : Own.treesMade P.codes (withOmega P.S) = some layO)
  (hS : P.S.sharedSplitNeeded = true) (hm : P.S.masksAhead = true)
include hG hU hlU hlO hS hm

/-- What is said of one member. i: its place in its sending; gs: for each message of that sending the groups that it joins. -/
def SeatTold (B : TreeBook) (m : Seat1) (sent : Array OracleNotice) (gs : List (List ℕ))
    (lay : TreeLay) (i : ℕ) : Prop :=
  ∃ o, G.oracleAt ((oraclesOf G.first.blocksInOrder).length + m.t) = some o ∧
    SeatIs (fun z => (oraclesOf G.first.blocksInOrder).length + z) B m
      ((oraclesOf G.first.blocksInOrder).length + m.t) (lay.part.getD i 0) o ∧
    o.tenants[lay.part.getD i 0]? = some (tenantOf sent gs i)

omit hG hU hlU hlO hS hm in
theorem seatTold_u (hG : oraclesOf G.shared.blocksInOrder = oraclesOf (chainOf c P tests last).blocksInOrder)
    (hU : withU P.S = some sentU) (hlU : Own.treesMade P.codes sentU = some layU)
    (hm : P.S.masksAhead = true) (B : TreeBook) (m : Seat1) (i : ℕ) (hi : i < sentU.size)
    (h : LaidIs B m 0 layU i) : SeatTold G B m sentU [[0], []] layU i :=
  seatIs_of_laid G P.codes sentU [[0], []] layU hlU (by rw [withU_size P.S sentU hm hU]; rfl) _ 0
    (fun τ o ho => by
      rw [Nat.add_zero]
      exact oracleAt_u G c P tests last sentU hG hU τ o ho)
    B m i hi h.tree h.part h.inBook h.shape

omit hm in
theorem seatTold_omega (B : TreeBook) (m : Seat1) (i : ℕ) (hi : i < (withOmega P.S).size)
    (h : LaidIs B m layU.shapes.size layO i) :
    SeatTold G B m (withOmega P.S) [[1], [1, 0]] layO i :=
  seatIs_of_laid G P.codes (withOmega P.S) [[1], [1, 0]] layO hlO
    (by rw [withOmega_size P.S hS]; rfl) _ layU.shapes.size
    (fun τ o ho => oracleAt_omega G c P tests last sentU hG hU layU hlU τ o ho)
    B m i hi h.tree h.part h.inBook h.shape

/-- **AT THE TEST ON G_u.** -/
theorem seatIs_nine (d : St) (hX : seatX P sentU layU layO 9 d = true)
    (hM : membX sentU.size 9 d = true) (π : P12) (t : T12)
    (ht : Seat.enter (·.gU) (·.firstMask) d = .ok t) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : Group) (Ly : GroupLayout) (D : Plain) (hf : Fixes π t a rest G0 Ly D) :
    D.mems.length = 2 ∧ ∀ q : Fin D.mems.length,
      (q.val = 0 ∧ (D.mems.get q).id = 0 ∧ SeatTold G D.book (D.mems.get q) sentU [[0], []] layU 0) ∨
      (q.val = 1 ∧ (D.mems.get q).id = sentU.size + 1 ∧
        SeatTold G D.book (D.mems.get q) (withOmega P.S) [[1], [1, 0]] layO 1) := by
  have sU := withU_size P.S sentU hm hU
  have sO := withOmega_size P.S hS
  obtain ⟨h2, hq⟩ := mems_at_nine P sentU layU layO d (by omega) (by omega) hX hM π t ht a rest G0 Ly
    D hf
  refine ⟨h2, fun q => ?_⟩
  rcases hq q with ⟨e, hid, hl⟩ | ⟨e, hid, hl⟩
  · exact .inl ⟨e, hid, seatTold_u G c P tests last sentU layU hG hU hlU hm _ _ 0 (by omega) hl⟩
  · exact .inr ⟨e, hid, seatTold_omega G c P tests last sentU layU layO hG hU hlU hlO hS _ _ 1
      (by omega) hl⟩

omit hm in
/-- **AT THE TEST ON G_omega.** -/
theorem seatIs_ten (d : St) (hX : seatX P sentU layU layO 10 d = true)
    (hM : membX sentU.size 10 d = true) (π : P12) (t : T12)
    (ht : Seat.enter (·.gOmega) (fun _ => none) d = .ok t) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) :
    D.mems.length = 2 ∧ ∀ q : Fin D.mems.length,
      (q.val = 0 ∧ (D.mems.get q).id = sentU.size ∧
        SeatTold G D.book (D.mems.get q) (withOmega P.S) [[1], [1, 0]] layO 0) ∨
      (q.val = 1 ∧ (D.mems.get q).id = sentU.size + 1 ∧
        SeatTold G D.book (D.mems.get q) (withOmega P.S) [[1], [1, 0]] layO 1) := by
  have sO := withOmega_size P.S hS
  obtain ⟨h2, hq⟩ := mems_at_ten P sentU layU layO d (by omega) hX hM π t ht a rest G0 Ly D hf
  refine ⟨h2, fun q => ?_⟩
  rcases hq q with ⟨e, hid, hl⟩ | ⟨e, hid, hl⟩
  · exact .inl ⟨e, hid, seatTold_omega G c P tests last sentU layU layO hG hU hlU hlO hS _ _ 0
      (by omega) hl⟩
  · exact .inr ⟨e, hid, seatTold_omega G c P tests last sentU layU layO hG hU hlU hlO hS _ _ 1
      (by omega) hl⟩

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.seatIs_nine
#print axioms VerifiableInference.Desc.K12.Coin.seatIs_ten
