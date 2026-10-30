-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FrontSeat.lean: A LAW ABOUT THE SEAT ProofFile.pureSeat
(Johnson/Desc/ProofFile/OnlineDescription.lean), NO PART OF IT: THE CHAIN's FIRST BLOCK, c.blocksInOrder[0], IS THE
IDLE FRONT: no round; a yes hands the record back.
OBJECT. c.first and c.blocksInOrder[0] of onlineDescription's first chain: ProofFile.chainBy's «match at_ .front with | some o => { o with name := frontName } | none => idleFront» (Johnson/Desc/ProofFile/Frames1.lean), the driver's address and guard around it, Chain.blocksInOrder's «bare».
USER. The link's frame's law (frame_kindTied's share hFront) · other files of this folder.
LETTERS. As in Johnson/IMR/K6Seat.lean.
CALLED, NOT TYPED: firstChain_shape (Johnson/Desc/First/Link/Law/Shape.lean).

  role_front_link   a place with the role «front» stands in no link.
  no_front          (AT EVERY o; NO PREMISE ON SCOPE) no member of the parts' frames bears the role
                    «front». WHY: the one block of the kind «frame» in no link that the seat's lots
                    lay is K13.lotEnd's chainEnd 1 5 true … (Johnson/IMR/BackSeat.lean: lot_end),
                    which HAS A ROUND; ProofFile.faultsOf
                    calls it a fault if a block of that kind with a round bears any role but «common»; an opening's seat has no fault.
  first_is          c.first = Block.guarded sameReply hearsReply { idleFront with place := frameAt none 0 }.
  front_of          c.blocksInOrder[0]? = some b with b.rounds = [] · b.name = frontName · b.place = (1, none, 0, frame) · b.planOk = true · b.decide s rs gs = ok t ↔ t = s.

What is not claimed. Nothing on a mark in the record: the idle front tests none. No soundness.
-/
import Johnson.IMR.BackSeat

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain FileDescription Place KindName roundlessBlock)
open VerifiableInference.Desc.First (S hearsReply frameAt)
open ProofFile (Cl)

/-- A place with the role «front» stands in no link. -/
theorem role_front_link {shape : List (String × Place)} {p : Place}
    (h : ProofFile.roleOf shape p = .front) : p.link = none := by
  unfold ProofFile.roleOf at h
  split at h
  · cases h
  · assumption
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h <;> cases h

theorem beq_front {r : ProofFile.FrameRole} (h : (r == ProofFile.FrameRole.front) = true) : r = .front := by
  cases r with
  | front => rfl
  | lay _ => exact nomatch h
  | clear _ => exact nomatch h
  | behind _ _ => exact nomatch h
  | common => exact nomatch h
  | stray => exact nomatch h

section
variable {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **No member of the parts' frames bears the role «front».** -/
theorem no_front (O : Open o pol lay KL F Z Bs base c A B) :
    ∀ x ∈ (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).frames, x.1 ≠ ProofFile.FrameRole.front := by
  intro x hx hr
  obtain ⟨-, -, -, hall⟩ := base_made O.made
  obtain ⟨L, hL, b, hb, hk, er, -⟩ := frames_from_lots hall hx
  have hrole : ProofFile.roleOf Bs.shape b.place = .front := er.symm.trans hr
  obtain ⟨-, rfl⟩ := lot_end hL hb hk (role_front_link hrole)
  have hm : ((VerifiableInference.Desc.ChainEnd.chainEnd 1 5 true (VerifiableInference.Desc.K13.inFrontOf Z)
      VerifiableInference.Desc.First.endAsks : Block S Unit).retype : Block S Cl) ∈
      Bs.all.flatMap fun x => x.2 := by
    rw [hall]
    exact List.mem_flatMap.2 ⟨(L, L.blocks Bs.G₀), List.mem_map.2 ⟨L, hL, rfl⟩, hb⟩
  have hf := O.sound
  simp only [ProofFile.faultsAt, ProofFile.faultsOf, List.append_eq_nil_iff, List.map_eq_nil_iff] at hf
  obtain ⟨⟨⟨⟨⟨⟨-, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hf
  have h3 := List.filterMap_eq_nil_iff.1 h2 _
    (List.mem_map.2 ⟨_, List.mem_filter.2 ⟨hm, by simpa using hk⟩, rfl⟩)
  dsimp only at h3
  rw [hrole] at h3
  split at h3
  · cases h3
  · split at h3
    · cases h3
    · rename_i hc
      exact hc rfl

/-- **The chain's first block is the idle front**, with the driver's address and guard. -/
theorem first_is (O : Open o pol lay KL F Z Bs base c A B) :
    c.first = Block.guarded ProofFile.sameReply hearsReply
      { (ProofFile.idleFront : Block S Cl) with place := frameAt none 0 } := by
  have hnf := no_front O
  have hc := O.chain
  unfold ProofFile.chainBy at hc
  dsimp only at hc
  have hfind : (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).frames.find?
      (fun x => x.1 == ProofFile.FrameRole.front) = none :=
    List.find?_eq_none.2 fun x hx hb => hnf x hx (beq_front hb)
  rw [hfind] at hc
  unfold ProofFile.chainC at hc
  split at hc
  · cases hc
  · dsimp only at hc
    split at hc
    · cases hc
    · rename_i c1 h1
      split at hc
      · cases hc
      · obtain rfl := Except.ok.inj hc
        obtain ⟨-, c0, ⟨hfirst, -, -, -, -⟩, rfl⟩ := VerifiableInference.Desc.Shape.firstChain_shape h1
        show Block.guarded _ hearsReply c0.first = _
        rw [hfirst]
        rfl

theorem sameReply_self (s : S) : ProofFile.sameReply s s = true := by
  unfold ProofFile.sameReply
  exact beq_self_eq_true _

/-- **THE FRONT's SEAT: c.blocksInOrder[0]**: at every o; no premise on scope. -/
theorem front_of (O : Open o pol lay KL F Z Bs base c A B) :
    ∃ b, c.blocksInOrder[0]? = some b ∧ b.rounds = [] ∧ b.name = ProofFile.frontName ∧
      b.place = { chain := 1, link := none, piece := 0, kind := .frame } ∧ b.planOk = true ∧
      ∀ s rs gs t, b.decide s rs gs = .ok t ↔ t = s := by
  refine ⟨{ c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter }, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show c.first.rounds = []
    rw [first_is O]
    rfl
  · show c.first.name = _
    rw [first_is O]
    rfl
  · show c.first.place = _
    rw [first_is O]
    rfl
  · show (c.first.planOk && c.first.hasNoClaimsAndNothingAfter) = true
    rw [first_is O]
    rfl
  · intro s rs gs t
    show c.first.decide s rs gs = .ok t ↔ _
    rw [first_is O]
    show ((Except.ok s : Except String S).bind (VerifiableInference.Desc.seatSame ProofFile.sameReply s)) = .ok t ↔ _
    show VerifiableInference.Desc.seatSame ProofFile.sameReply s s = .ok t ↔ _
    unfold VerifiableInference.Desc.seatSame
    rw [sameReply_self, if_pos rfl]
    constructor
    · intro h
      exact (Except.ok.inj h).symm
    · rintro rfl
      rfl

end

end IM

#print axioms IM.no_front
#print axioms IM.first_is
#print axioms IM.front_of
