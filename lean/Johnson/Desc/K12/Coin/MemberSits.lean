-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/MemberSits.lean: **AT THE SHARED CHAIN's TWO PROXIMITY TESTS EACH MEMBER OF THE GROUP UNDER TEST SITS, IN THE FILE's NUMBERING, AT THE TABLE's TENANT OF ITS MESSAGE.** Statements; each proof is a call of
MembersLaid.lean and the text of tenantSh (Johnson/Desc/Sound/SharedMembers.lean).
  sits_nine   under sharedX 9: D has two members: the 0-th bears o_u's number and (noAt t₁ t₂ 1 m.t, m.part) = tenantSh t₁ layU layO .oU; the 1-st o_sp's, at .oSp.
  sits_ten    under sharedX 10: o_omega's and o_sp's.
So a member x of msSh … t₁ … that sits at the tenant of μ, and the record's member m with μ's number, have ONE seat: x.1.seat x.2 = (noAt t₁ t₂ 1 m.t, m.part).
Limits: those of MembersLaid.lean and SharedMembers.lean. At lo := t₁. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Coin.MembersLaid
import Johnson.Desc.K12.Coin.GameBook
import Johnson.Desc.Sound.SharedMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared (Msg2)
open H2K.First (Plain Seat1)
open _root_.Desc.K14 (St P14 withOmega)
open _root_.Desc.K14.Law.Fence (sharedX sharedX_parts tenantSh numSh)

/-- The seat of a member of the record, in the file's numbering on the shared chain. -/
abbrev seatAt (t₁ t₂ : ℕ) (m : Seat1) : ℕ × ℕ := (noAt t₁ t₂ 1 m.t, m.part)

theorem seat_u (t₁ t₂ : ℕ) (B : TreeBook) (m : Seat1) (layU layO : TreeLay)
    (h : LaidIs B m 0 layU 0) : seatAt t₁ t₂ m = tenantSh t₁ layU layO .oU := by
  show (t₁ + m.t, m.part) = (t₁ + layU.tree.getD 0 0, layU.part.getD 0 0)
  rw [h.tree, h.part, Nat.zero_add]

theorem seat_omega (t₁ t₂ : ℕ) (B : TreeBook) (m : Seat1) (layU layO : TreeLay)
    (h : LaidIs B m layU.shapes.size layO 0) : seatAt t₁ t₂ m = tenantSh t₁ layU layO .oOmega := by
  show (t₁ + m.t, m.part) = (t₁ + layU.shapes.size + layO.tree.getD 0 0, layO.part.getD 0 0)
  rw [h.tree, h.part, Nat.add_assoc]

theorem seat_sp (t₁ t₂ : ℕ) (B : TreeBook) (m : Seat1) (layU layO : TreeLay)
    (h : LaidIs B m layU.shapes.size layO 1) : seatAt t₁ t₂ m = tenantSh t₁ layU layO .oSp := by
  show (t₁ + m.t, m.part) = (t₁ + layU.shapes.size + layO.tree.getD 1 0, layO.part.getD 1 0)
  rw [h.tree, h.part, Nat.add_assoc]

/-- **AT THE TEST ON G_u.** -/
theorem sits_nine (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (t₁ t₂ : ℕ) (d : St)
    (hU : 0 < sentU.size) (hO : 1 < (withOmega P.S).size)
    (hX : sharedX P sentU layU layO 9 d = true) (π : P12) (t : T12)
    (ht : Seat.enter (·.gU) (·.firstMask) d = .ok t) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : Group) (Ly : GroupLayout) (D : Plain) (hf : Fixes π t a rest G0 Ly D) :
    D.mems.length = 2 ∧ ∀ q : Fin D.mems.length,
      (q.val = 0 ∧ (D.mems.get q).id = numSh sentU.size .oU ∧
        seatAt t₁ t₂ (D.mems.get q) = tenantSh t₁ layU layO .oU) ∨
      (q.val = 1 ∧ (D.mems.get q).id = numSh sentU.size .oSp ∧
        seatAt t₁ t₂ (D.mems.get q) = tenantSh t₁ layU layO .oSp) := by
  obtain ⟨_, hs, hM, _⟩ := (sharedX_parts P sentU layU layO 9 d).1 hX
  obtain ⟨h2, hq⟩ := mems_at_nine P sentU layU layO d hU hO hs hM π t ht a rest G0 Ly D hf
  refine ⟨h2, fun q => ?_⟩
  rcases hq q with ⟨e, hid, h⟩ | ⟨e, hid, h⟩
  · exact .inl ⟨e, hid, seat_u t₁ t₂ _ _ layU layO h⟩
  · exact .inr ⟨e, hid, seat_sp t₁ t₂ _ _ layU layO h⟩

/-- **AT THE TEST ON G_omega.** -/
theorem sits_ten (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (t₁ t₂ : ℕ) (d : St)
    (hO : 1 < (withOmega P.S).size) (hX : sharedX P sentU layU layO 10 d = true) (π : P12) (t : T12)
    (ht : Seat.enter (·.gOmega) (fun _ => none) d = .ok t) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) :
    D.mems.length = 2 ∧ ∀ q : Fin D.mems.length,
      (q.val = 0 ∧ (D.mems.get q).id = numSh sentU.size .oOmega ∧
        seatAt t₁ t₂ (D.mems.get q) = tenantSh t₁ layU layO .oOmega) ∨
      (q.val = 1 ∧ (D.mems.get q).id = numSh sentU.size .oSp ∧
        seatAt t₁ t₂ (D.mems.get q) = tenantSh t₁ layU layO .oSp) := by
  obtain ⟨_, hs, hM, _⟩ := (sharedX_parts P sentU layU layO 10 d).1 hX
  obtain ⟨h2, hq⟩ := mems_at_ten P sentU layU layO d hO hs hM π t ht a rest G0 Ly D hf
  refine ⟨h2, fun q => ?_⟩
  rcases hq q with ⟨e, hid, h⟩ | ⟨e, hid, h⟩
  · exact .inl ⟨e, hid, seat_omega t₁ t₂ _ _ layU layO h⟩
  · exact .inr ⟨e, hid, seat_sp t₁ t₂ _ _ layU layO h⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.sits_nine
#print axioms VerifiableInference.Desc.K12.Coin.sits_ten
