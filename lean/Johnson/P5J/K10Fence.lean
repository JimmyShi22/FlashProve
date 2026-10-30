-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Fence.lean: THE FIELD fence OF K10's DEBT AT THE CLOSED CONSTANT (`AtMgA.K10Debt`,
Johnson/P5J/K10Debt.lean) FROM ANOTHER FILE's INVARIANT ALONG THE FOLD, DOWN TO THAT FILE's ONE
NAMED DEBT. Statements and proofs: calls; one evaluation by the kernel.

What is said, at h : AtMgA OnBytes.secondHashFunction ..:
  `k10_in_room`: every place of the kind K10 in `At.ps` has a number from 3 to 355: by the kernel.
  `k10_fence_at`: `P1L20.RoomOwes cF (F0T ..).start₁ free0` (Johnson/P1L20R/RoomFold.lean: what is
    left of "the index masks' message's ledger is there and open, and that message is a member of no
    group" along the first chain) gives the field fence, to the letter: at every state with
    `h.toAtMg.rch i s`, i a place of the kind K10: the index masks' message is a member of no group.
    By `room_out_of_groups`, `outOfGroupsB_iff` (same file) and `reach_raw`
    (Johnson/Top/H0/Walk/Reach.lean).
Limits. `RoomOwes` IS A PREMISE: shown of nothing here: its field make speaks of the sub-protocol at
number 2; its field keep of the numbers of the kinds other than the frame's: K10's own share of keep
lies (`room_close_all`, Johnson/LPFK10R/HeadLinkJoins.lean: another form: not joined here). free0 is
a letter. AT OnBytes.secondHashFunction ALONE. Nothing on soundness.

-/
import Johnson.P5J.K10Debt
import Johnson.P1L20R.RoomFold

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
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (OutF)
open VerifiableInference.Desc.Kinds.Head.Law (ps_length)
open Johnson.Desc.First.Walk.Tied (reach_raw)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

set_option quotPrecheck false in
/-- Its statements' type. -/
local notation "ST" => (ProofFile.InstPub × TS) × (Frame.E FR).Str

theorem k10_in_room_all : ((List.range 358).all fun i => (At.ps[i]?).all fun a =>
    a.kind != KindName.K10 || (decide (3 ≤ i) && decide (i ≤ 355))) = true := by decide +kernel

/-- Every place of the kind K10 has a number from 3 to 355. -/
theorem k10_in_room (i : ℕ) (a : Place) (ha : At.ps[i]? = some a)
    (hk : a.kind = KindName.K10) : 3 ≤ i ∧ i ≤ 355 := by
  have hi : i < 358 := ps_length ▸ (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 k10_in_room_all i (List.mem_range.2 hi)
  rw [ha] at h
  simpa [hk] using h

/-- **THE FIELD fence, FROM THE ONE NAMED DEBT `P1L20.RoomOwes`.** -/
theorem k10_fence_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {free0 : ℕ}
    (H : P1L20.RoomOwes cF (F0T OnBytes.secondHashFunction Zp Np cF).start₁ free0) :
    ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
      ∀ s : ST, h.toAtMg.rch i s → OutF s.1.2 := by
  intro i a ha hk s hs
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨h3, h355⟩ := k10_in_room i a ha hk
  have hp : ∀ b ∈ cF.blocksInOrder, b.planOk = true := fun b hb =>
    (Eq.mp (Bool.and_eq_true _ _) (List.all_eq_true.1
      (planOk_parts (F0T OnBytes.secondHashFunction Zp Np cF) h.laid.planOk).1 b hb)).1
  exact P1L20.outOfGroupsB_iff.1
    (P1L20.room_out_of_groups h.scope h.reads O hp H (reach_raw hs.1) h3 h355)

end P5J

#print axioms P5J.k10_in_room
#print axioms P5J.k10_fence_at
