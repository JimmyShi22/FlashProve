-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFGuard/Strike.lean: WHAT IS LAID FOR THE PROOF FILE IS THE SAME WITH THE GUARD's TEST ON
THE REPLY AND WITHOUT IT: the proofs of the six statements of Johnson/LPFGuard/Unguarded.lean.
Statements there; proofs here. Nothing of the library's text is struck.

Main names, in the file's order.
* `idle_block`, `idle_chain`, `idle_first`: at a test that always says yes the guard is the identity
  (Driver.lean, Idle.lean).
* `guarded_reply`: one block's guard at the seat's test falls where the block's decision and its
  runs leave the reply.
* `h1_same`: PLACE (c): `h1Bare G = ProofFile.h1Own G`: the first half of the block at "H:1" is K2's step
  that enters the head's segment, which leaves the reply (`seatBut_reply.front`) and has no runs
  (the library's `runsLeave_of_bare`, Johnson/Desc/Sound/StillOfLeaves.lean).
  `thePureBare_eq`, `bareSeat_eq`: so the unguarded lots ARE the seat's lots, and the unguarded seat
  is the seat with the field `same` turned.
* `desc_alike`: PLACES (a) AND (b): `pureZ_alike` (Seat.lean) at the proof file's seat: its premises
  are supplied by `thePure_but` (Lots.lean) over `seatBut_reply` (Makers.lean), and by the library's
  `ProofFile.Law.pubBy_fields` (Johnson/Desc/ProofFile/Law/PlainMade.lean): the table of steps of a public
  part that is made is `cutOf`'s.
* `strike_desc`; `strike` (THE STRIKE), with `laidOfDesc_alike` (AlikeLaid.lean); `strike_the`.

Limits. Unguarded.lean's eleven, whole. Above all: the top statement stops at `proofDataAndDecisionOrRefusalAt`; the
strike carries a theorem over to the unguarded description and does not free that theorem's proof
of the guard; nothing on the programs' verifier; nothing on soundness.

For proofs only; no program imports this file.


-/
import Johnson.LPFGuard.Makers
import Johnson.LPFGuard.Lots
import Johnson.LPFGuard.Seat
import Johnson.LPFGuard.AlikeLaid
import Johnson.LPFGuard.Idle
import Johnson.Desc.ProofFile.Law.PlainMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFGuard

open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Lot Ground PureSeat SecondHashFunctionArgument)

/-! ## The idle guard -/

theorem idle_block : Spec.idle_block := fun but b => guarded_idle_self (fun _ _ => rfl) but b

theorem idle_chain : Spec.idle_chain := fun but c => chainGuarded_idle (fun _ _ => rfl) but c

theorem idle_first : Spec.idle_first := fun H links several hs =>
  firstChain_idle H hs links several

/-! ## Place (c): the first half of the block at "H:1" -/

/-- One block's guard at the seat's test falls where the block's decision and its runs leave the
reply. -/
theorem guarded_reply {Cl : Type} {b : Block S Cl} (hd : b.Leaves hR) (hr : b.RunsLeave hR)
    (but : Place → Bool) : b.guarded ProofFile.sameReply but = b := by
  rw [sameReply_sameBy]
  exact guarded_self hd hr but

theorem h1_same (G : Ground) : h1Bare G = ProofFile.h1Own G := by
  unfold h1Bare ProofFile.h1Own
  dsimp only
  rw [guarded_reply (fun s _ _ s' h => seatBut_reply.front _ s s' h)
    (runsLeave_of_bare hR rfl)]

theorem thePureBare_eq (Z : ProofFile.Pub) : thePureBare Z = ProofFile.onlineFirstChainBlockTables Z := by
  have e : h1Bare = ProofFile.h1Own := funext h1_same
  unfold thePureBare ProofFile.onlineFirstChainBlockTables p4Bare ProofFile.p4Pure
  rw [e]

theorem bareSeat_eq (o : SecondHashFunctionArgument) (Z : ProofFile.Pub) :
    bareSeat o Z = { ProofFile.pureSeat o Z with same := fun _ _ => true } := by
  unfold bareSeat
  rw [thePureBare_eq]
  rfl

/-! ## The two descriptions -/

theorem desc_alike (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) :
    AlikeE Alike (ProofFile.onlineDescription o pol lay KL) (descBare o pol lay KL) := by
  rw [descPure_unfolds]
  unfold descBare
  cases hZ : ProofFile.pureRoad.pub o pol lay KL with
  | error e => exact rfl
  | ok Z =>
    show AlikeE Alike (ProofFile.onlineDescriptionFromPublicPart Z (ProofFile.pureSeat o Z)) (ProofFile.onlineDescriptionFromPublicPart Z (bareSeat o Z))
    rw [bareSeat_eq]
    exact pureZ_alike rfl (fun _ _ => rfl)
      (fun G => thePure_but replyR_refl replyR_trans seatBut_reply Z G)
      ⟨_, (ProofFile.Law.pubBy_fields
        (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from hZ)).2.2.2.1⟩

theorem strike_desc : Spec.strike_desc := by
  intro o pol lay KL
  have h := desc_alike o pol lay KL
  revert h
  cases ProofFile.onlineDescription o pol lay KL <;> cases descBare o pol lay KL <;> exact id

/-- **THE STRIKE**: what is laid for the proof file is the same without the guard as with it, at all
bytes for the three public files and every function o in the place of the second hash function. -/
theorem strike : Spec.strike := by
  intro o pol lay KL
  have h := desc_alike o pol lay KL
  unfold laidPBare LPFD.Full.proofDataAndDecisionOfPublicFiles
  revert h
  cases ProofFile.onlineDescription o pol lay KL <;> cases descBare o pol lay KL <;> intro h
  · have e : _ = _ := h
    rw [e]
  · exact h.elim
  · exact h.elim
  · exact laidOfDesc_alike h o pol lay KL

theorem strike_the : Spec.strike_the := fun o Zk => (strike o Zk.pol Zk.lay Zk.KL).symm

end LPFGuard

#print axioms LPFGuard.idle_block
#print axioms LPFGuard.idle_chain
#print axioms LPFGuard.idle_first
#print axioms LPFGuard.h1_same
#print axioms LPFGuard.thePureBare_eq
#print axioms LPFGuard.desc_alike
#print axioms LPFGuard.strike_desc
#print axioms LPFGuard.strike
#print axioms LPFGuard.strike_the
