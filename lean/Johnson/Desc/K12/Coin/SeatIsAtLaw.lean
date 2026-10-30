-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/SeatIsAtLaw.lean: **SeatIs AT EVERY MEMBER OF THE SHARED CHAIN's TWO PROXIMITY TESTS, AT THE NUMBERING AT WHICH THE KIND's LAW IS CALLED (noAt t₁ t₂ 1), FROM THE ONE X.** Statements; each proof is a
call of SeatIsAtTests.lean with three small joints.
  noAt_one        noAt t₁ t₂ 1 = (t₁ + ·): by the text of numAt (Johnson/Desc/BlockSlot.lean).
  SeatToldAt      SeatTold (SeatIsAtTests.lean) with noAt t₁ t₂ 1 in the place of ((the number of trees that the first chain's blocks tell) + ·).
  seatIs_nine_X | seatIs_ten_X   under sharedX 9 | 10 (Johnson/Desc/Sound/SharedX.lean) in the place of seatX and membX · THE TWO LAYOUTS ASKED ONCE, as layTrees (the other spelling by Own.treesMade_eq) · hlo: the first
                  chain's blocks tell t₁ trees.
WHAT IS NOT SPENT HERE, AND WHERE IT IS: that the tree at the book's place z BEARS the number firstTree + z (BookOrd: in sharedX's bookX: spent by the law's own promise, GameHeldBook.lean).
Limits: those of SeatIsAtTests.lean. hlo and hG are premises. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Coin.SeatIsAtTests
import Johnson.Desc.K12.Coin.GameBook
import Johnson.Desc.Sound.SharedX

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.First (Plain Seat1)
open _root_.Desc.K14 (St P14 chainOf withU withOmega)
open _root_.Desc.K14.Law.Fence (sharedX sharedX_parts)

theorem noAt_one (t₁ t₂ : ℕ) : noAt t₁ t₂ 1 = fun z => t₁ + z := rfl

/-- What is said of one member, at the law's numbering. -/
def SeatToldAt {Xi : Type} (G : FileDescription Xi) (t₁ t₂ : ℕ) (B : TreeBook) (m : Seat1)
    (sent : Array OracleNotice) (gs : List (List ℕ)) (lay : TreeLay) (i : ℕ) : Prop :=
  ∃ o, G.oracleAt (noAt t₁ t₂ 1 m.t) = some o ∧
    SeatIs (noAt t₁ t₂ 1) B m (noAt t₁ t₂ 1 m.t) (lay.part.getD i 0) o ∧
    o.tenants[lay.part.getD i 0]? = some (tenantOf sent gs i)

theorem seatToldAt_of {Xi : Type} (G : FileDescription Xi) (t₁ t₂ : ℕ)
    (hlo : (oraclesOf G.first.blocksInOrder).length = t₁) (B : TreeBook) (m : Seat1)
    (sent : Array OracleNotice) (gs : List (List ℕ)) (lay : TreeLay) (i : ℕ)
    (h : SeatTold G B m sent gs lay i) : SeatToldAt G t₁ t₂ B m sent gs lay i := by
  unfold SeatTold at h
  rw [hlo] at h
  exact h

section
variable {Xi : Type} (G : FileDescription Xi) (c : Model.Verify.Chains) (P : P14)
  (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
  (sentU : Array OracleNotice) (layU layO : TreeLay) (t₁ t₂ : ℕ)
  (hG : oraclesOf G.shared.blocksInOrder = oraclesOf (chainOf c P tests last).blocksInOrder)
  (hlo : (oraclesOf G.first.blocksInOrder).length = t₁)
  (hU : withU P.S = some sentU) (hlU : layTrees P.codes sentU = some layU)
  (hlO : layTrees P.codes (withOmega P.S) = some layO)
  (hS : P.S.sharedSplitNeeded = true) (hm : P.S.masksAhead = true)
include hG hlo hU hlU hlO hS hm

/-- **AT THE TEST ON G_u.** -/
theorem seatIs_nine_X (d : St) (hX : sharedX P sentU layU layO 9 d = true) (π : P12) (t : T12)
    (ht : Seat.enter (·.gU) (·.firstMask) d = .ok t) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : Group) (Ly : GroupLayout) (D : Plain) (hf : Fixes π t a rest G0 Ly D) :
    D.mems.length = 2 ∧ ∀ q : Fin D.mems.length,
      (q.val = 0 ∧ (D.mems.get q).id = 0 ∧
        SeatToldAt G t₁ t₂ D.book (D.mems.get q) sentU [[0], []] layU 0) ∨
      (q.val = 1 ∧ (D.mems.get q).id = sentU.size + 1 ∧
        SeatToldAt G t₁ t₂ D.book (D.mems.get q) (withOmega P.S) [[1], [1, 0]] layO 1) := by
  obtain ⟨_, hs, hM, _⟩ := (sharedX_parts P sentU layU layO 9 d).1 hX
  obtain ⟨h2, hq⟩ := seatIs_nine G c P tests last sentU layU layO hG hU
    ((Own.treesMade_eq _ _).trans hlU) ((Own.treesMade_eq _ _).trans hlO) hS hm d hs hM π t ht a rest
    G0 Ly D hf
  refine ⟨h2, fun q => ?_⟩
  rcases hq q with ⟨e, hid, h⟩ | ⟨e, hid, h⟩
  · exact .inl ⟨e, hid, seatToldAt_of G t₁ t₂ hlo _ _ _ _ _ _ h⟩
  · exact .inr ⟨e, hid, seatToldAt_of G t₁ t₂ hlo _ _ _ _ _ _ h⟩

omit hm in
/-- **AT THE TEST ON G_omega.** (That X 10 is reached wants the masks ahead: sharedX_k14.) -/
theorem seatIs_ten_X (d : St) (hX : sharedX P sentU layU layO 10 d = true) (π : P12) (t : T12)
    (ht : Seat.enter (·.gOmega) (fun _ => none) d = .ok t) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) :
    D.mems.length = 2 ∧ ∀ q : Fin D.mems.length,
      (q.val = 0 ∧ (D.mems.get q).id = sentU.size ∧
        SeatToldAt G t₁ t₂ D.book (D.mems.get q) (withOmega P.S) [[1], [1, 0]] layO 0) ∨
      (q.val = 1 ∧ (D.mems.get q).id = sentU.size + 1 ∧
        SeatToldAt G t₁ t₂ D.book (D.mems.get q) (withOmega P.S) [[1], [1, 0]] layO 1) := by
  obtain ⟨_, hs, hM, _⟩ := (sharedX_parts P sentU layU layO 10 d).1 hX
  obtain ⟨h2, hq⟩ := seatIs_ten G c P tests last sentU layU layO hG hU
    ((Own.treesMade_eq _ _).trans hlU) ((Own.treesMade_eq _ _).trans hlO) hS d hs hM π t ht a rest
    G0 Ly D hf
  refine ⟨h2, fun q => ?_⟩
  rcases hq q with ⟨e, hid, h⟩ | ⟨e, hid, h⟩
  · exact .inl ⟨e, hid, seatToldAt_of G t₁ t₂ hlo _ _ _ _ _ _ h⟩
  · exact .inr ⟨e, hid, seatToldAt_of G t₁ t₂ hlo _ _ _ _ _ _ h⟩

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.noAt_one
#print axioms VerifiableInference.Desc.K12.Coin.seatIs_nine_X
#print axioms VerifiableInference.Desc.K12.Coin.seatIs_ten_X
