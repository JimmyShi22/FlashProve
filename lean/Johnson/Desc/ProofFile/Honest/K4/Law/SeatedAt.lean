-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SeatedAt.lean: CONDITIONAL. Statements with their proofs; no
definition.

What is here. THREE FIELDS OF THE HYPOTHESIS `K4Seated` (Law/Seated.lean): THE MEMBER's PLACE,
ROUNDS AND ORACLE MESSAGES: AT A MEMBER THAT IS K4's LOT's OWN SUB-PROTOCOL, SEATED ALONE AS THE
DESCRIPTION SEATS IT. K4 is the sub-protocol of the feed-forward layers' own rounds. The proofs are
calls of the library's `IM.alone_place`, `IM.alone_rounds`, `IM.alone_oracles`
(Johnson/IMR/SeatForm.lean), and unfolding.

  h: blk is `IM.seatedAs` of K4's lot's sub-protocol at the parameters x (`ProofFile.k4Block x`), alone,
      under some name at K4's place of group g (`IM.LaidAlone`).
  `laid_rounds`, `laid_oracles`   under h: blk's rounds are the verifier's at the parameters x.2
      with the flag that the lookup states its own claims; no round has an oracle message.
  `laid_place`   under h, where the public data's link is 2 g and its piece 3: blk stands at the
      public data's place.
  `k4Seated_of_laid`   **so K4Seated, from h, the six other fields and two equations.**

Not shown here. THAT A THREAD's MEMBER IS SO SEATED: h is a hypothesis: an equation on the member.
THE SIX OTHER FIELDS (member, own, seg, half, front, fits): `k4Seated_of_laid` takes them as they
stand, and two equations on the public data besides (its group is g; its piece is 3). This file
gives no example of these hypotheses together. Following import lines, and stopping unopened at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module
whose name begins Cb.Bridge, its imports reach 2 modules under Johnson/Goal/ and 2 under
Johnson/Bridge/, and none of the others; what lies behind the four is not counted; 7 of the modules
that it reaches have RecCompile in their names. Nothing on soundness, on completeness or on any
other property.

Kin. The library has the lot's sub-protocol's own fields without a seat: `k4Block_rounds`,
`k4Block_oracles` (Johnson/Road/K4/K4CutRows.lean: in the spelling of the table's entries),
`k4Block_place` (Johnson/Road/K4/K4LotSkel.lean) and `k4Block_is` (Johnson/Road/K4/K04Sits.lean: the
lot's sub-protocol is `blockAtC` at its parameters, but for the test on the plan). AT A SEATED
MEMBER it has the rounds, in the spelling of the table's entries: `declares_alone`
(Johnson/Road/K4/K04Sits.lean: under the like h, at every `same` and address). What is here lays
these at a seated member, in `K4Seated`'s own spelling; none of the five is called: the proofs
unfold.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Seated
import Johnson.IMR.K4Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par blockAtC)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Block Claim First.S)

variable {blk : Block First.S Claim} {x : Bool × Par} {name : String} {g : Nat}

/-- The member's rounds are the verifier's. CONDITIONAL: on h. -/
theorem laid_rounds (h : IM.LaidAlone ProofFile.sameReply blk (ProofFile.k4Block x) name (IM.k4Place g)) :
    blk.rounds = (blockAtC { x.2 with k3Runs := true }).rounds := by
  rw [IM.alone_rounds h]
  rfl

/-- No round of the member has an oracle message. CONDITIONAL: on h. -/
theorem laid_oracles (h : IM.LaidAlone ProofFile.sameReply blk (ProofFile.k4Block x) name (IM.k4Place g)) :
    blk.oracles = blk.rounds.map fun _ => [] := by
  rw [IM.alone_oracles h, IM.alone_rounds h]
  dsimp only [ProofFile.k4Block, OnBytes.Desc.First.K4.blockAtC, OnBytes.Desc.First.K4.atClaims,
    OnBytes.Desc.First.K4.blockAtS, VerifiableInference.Desc.Block.liftPart,
    OnBytes.Desc.First.K4.block]
  rw [List.map_map]
  exact List.map_congr_left fun _ _ => rfl

/-- The member stands at the public data's place. CONDITIONAL: on h and two equations on the public
data. -/
theorem laid_place (h : IM.LaidAlone ProofFile.sameReply blk (ProofFile.k4Block x) name (IM.k4Place g))
    {Q : K4Pub} (hl : Q.link = 2 * g) (hp : Q.piece = 3) : blk.place = k4Place Q := by
  rw [IM.alone_place h]
  unfold k4Place
  rw [hl, hp]

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub}

/-- **`K4Seated` at a member that is the lot's own sub-protocol, seated alone.** CONDITIONAL: on h,
on the six fields that h does not give, and on two equations on the public data. -/
theorem k4Seated_of_laid
    (h : IM.LaidAlone ProofFile.sameReply blk (ProofFile.k4Block x) name (IM.k4Place g))
    (member : T.bs[b]? = some blk)
    (own : x.2.P = Q.P ∧ x.2.hp = Q.hp ∧ x.2.g = Q.g ∧ x.2.link = Q.link ∧ x.2.piece = Q.piece)
    (seg : Q.seg = Q.link ∧ Q.link = 2 * Q.g) (hg : Q.g = g) (hp : Q.piece = 3)
    (half : T.hs.find? (fun z => z.place == blk.place) =
      some (k4Half cells weights tokens look Q))
    (front : Q.r0 = T.front + roundsTo T.bs b)
    (fits : ∀ fr w, drawsFit (T.ahead ++ declsTo T.bs b) fr = true → T.valid w →
      k4Fits Q (look Q fr) (tokens w.x) = true) :
    K4Seated T b cells weights tokens look Q { x.2 with k3Runs := true } blk :=
  { member := member
    place := laid_place h (by rw [seg.2, hg]) hp
    rounds := laid_rounds h
    oracles := laid_oracles h
    own := own
    seg := seg
    half := half
    front := front
    fits := fits }

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.laid_rounds
#print axioms ProofFile.Honest.K4.laid_oracles
#print axioms ProofFile.Honest.K4.laid_place
#print axioms ProofFile.Honest.K4.k4Seated_of_laid
