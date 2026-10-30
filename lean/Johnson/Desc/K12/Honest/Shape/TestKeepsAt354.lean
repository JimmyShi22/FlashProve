-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestKeepsAt354.lean: what a proximity test keeps, at the first chain's
state (`K12KeepsFirst`, Johnson/Desc/K12/Honest/Shape/TestKeepsFirst.lean), is proved at number 354
of the flat list of the proof file's first chain, from an accepting step of the block at that
number. Six lemmas, each under one structure of hypotheses, `P5J.AtMg` (Johnson/P5J/AtMg.lean;
below: the head), in five of the six at the format's second hash function `OnBytes.secondHashFunction`. General in the
head's other parameters and in the states s and s'; `k12KeepsFirst_at_354` also in ft. The
verifier's state alone: no prover, no coin, no frame for an honest side.

For what. `k12Keeps_form_354` has the form of one clause of a definition of what a step of the first
chain keeps, kind by kind. Such a definition has `K12KeepsFirst p12` as its clause at the kind K12,
and that clause has to be shown at number 354 from an accepting step at every state in which no test
is marked as failed. The definition is not part of this library. The lemmas here give the clause,
and say which `p12`. Johnson/Desc/K12/Honest/Shape/TestKeepsPile.lean, which imports this file,
calls `answers_at_head`.

Terms. A chain (`Chain`, Johnson/Desc/Block.lean) makes a flat list (`Chain.blocksInOrder`) of blocks
(`Block`: a sub-protocol at one place), numbered from 0. `cF` is the head's parameter for the first
chain of the proof file's description (`P5J.F0T`, Johnson/P5J/AtTerm.lean). A block's address is its
field `place` (`Place`: chain, link, piece, kind). A step of blk from s to s' accepts where
`StepYes ft blk s s'` holds (Johnson/Top/H0/Walk/Reach.lean): `blk.step ft` returns s', at as many
rounds as blk declares and at columns all of which it reads. ft, the first argument of `Block.step`
(Johnson/Desc/Block.lean), is the number of the chain's first own tree. s and s' are states of the
first chain (`S`, Johnson/Desc/First/State.lean): s before the block, s' after it. A test is marked
as failed in s where `s.failed` is not `none`. The frame for an honest side is
Johnson/Desc/ProofFile/Honest/Frame.lean.

  `k12KeepsFirst_at_354`: under the head, where `cF.blocksInOrder[354]? = some blk` and `StepYes ft blk s s'`
    hold: `K12KeepsFirst (H2U.p12OfMade Zp.made) s s'` holds. At every ft and at all states s and s'
  `k12Keeps_form_354`: the kind and the clause in one statement. Under the head, for every blk with
    `cF.blocksInOrder[354]? = some blk`: `blk.place.kind` is `KindName.K12`, and from `s.failed = none` and
    `StepYes 0 blk s s'`: `K12KeepsFirst (H2U.p12OfMade Zp.made) s s'` holds
  `member_at_354`: under the head the flat list has a block at number 354: there is a blk with
    `cF.blocksInOrder[354]? = some blk`
  `place_at_354`: under the head, the address of the block at number 354 is `⟨1, none, 2, .K12⟩`:
    chain 1, in no link, piece 2, kind K12
  `answers_at_head`: under the head `(H2U.p12OfMade Zp.made).answers = 1`: a sample has one answer
    (`P12.answers`, Johnson/Desc/K12/Frame.lean: the answers to an out-of-domain sample)
  `p12_at_head`: under the head, at every earlier hash o: `H2U.p12OfMade Zp.made` is
    `H2K.JointK.pL Np` (Johnson/Desc/K12/Law/SitsChains.lean)

The parameter. `p12` is `H2U.p12OfMade Zp.made` (Johnson/Desc/K12/AtPlan.lean), where `Zp` is the
head's public part, of type `ProofFile.Pub` (Johnson/Desc/ProofFile/Pub.lean). The head's parameter `Z` is
not meant: it is of type `VerifierAndGoals.PublicFiles` (Ladder/Stored.lean), the three public files, which has no
field `made`.

By what. All six proofs are calls of the library's lemmas. The head's field `laid` (`LaidAt`,
Johnson/P5J/LaidOpens.lean) has a field `opened`, which gives `IM.Open` (Johnson/IMR/SeatOpen.lean),
a hypothesis of the lemmas of the namespace `IM`. `IM.at_354` (Johnson/IMR/LastFour.lean) brings an
accepting step at number 354 down to an accept of `K12.atFinish (H2U.p12OfMade Zp.made)`
(Johnson/Desc/K12/AtFinish.lean): it passes the change of the type of claims (`Block.retype`), the
guard on the mark (`ProofFile.guardMark`), the chain's guard (`Block.guarded`) and the flat list's added
test on the plan (`Block.hasNoClaimsAndNothingAfter`). `IM.back_of` and `IM.back_numbers` (Johnson/IMR/BackSeat.lean) give
the block: number 1 of `cF.back`, the blocks after the links, is number 353 + 1 of the flat list.
`IM.alone_place` (Johnson/IMR/SeatForm.lean) gives its address. `IM.blocksOk_of_planOk`
(Johnson/IMR/PlanOkFlat.lean), `IM.hp_of_planOk` (Johnson/IMR/SendsFinal.lean) and
`H2K.JointK.answers_of_planOk` (Johnson/Desc/K12/Law/Top.lean) give "one answer" from the
description's own test on the plan, which is the field `planOk` of `LaidAt`. Then
`k12KeepsFirst_of_yes` (TestKeepsFirst.lean) gives the clause. `p12_at_head` is
`H2K.JointK.p12OfMade_is` (Johnson/Loose/H2K12/LaterSeatsN.lean) at the field `places` of `LaidAt`.

Hypotheses of `k12KeepsFirst_at_354`. h: the head at `OnBytes.secondHashFunction`; of its five fields the proofs
of this file read `scope` (`VerifierAndGoals.InScope Z = true`, Ladder.lean), `reads` (what
`VerifierAndGoals.readFiles Z` returns) and `laid`. hb: blk is the block at number 354 of `cF.blocksInOrder`. hy:
`StepYes ft blk s s'`.

Limits.
- All limits of TestKeepsFirst.lean hold here too.
- `k12KeepsFirst_at_354` has no hypothesis on the state before the block: no mark on its rows is
  asked for, and "no test is marked as failed before the block" is not asked for either, since
  `K12KeepsFirst` itself gives it (`K12KeepsFirst.unmarked`). `k12Keeps_form_354` has that
  hypothesis because the form has it, and its proof does not use it.
- `k12Keeps_form_354` is stated at ft = 0 only.
- `place_at_354` states `link := none`, which `Place` has before the links as well as after them.
  That the block is one of those after the links is in the proof only.
- The lemmas hold where the head holds; this file gives no values that meet the head. (The side
  library AtFullSide states that there are values that meet the stronger structure `P5J.AtMgA`,
  Johnson/P5J/MgAtAll.lean, at the stored full-size files: `AtFullSide.Top.headMember_zFull`,
  AtFullSide/Top/HeadMemberAtFull.lean. `AtMgA` extends `AtMg`, so these values meet `AtMg` too.)
- That any step at number 354 accepts is not shown here.
- The full size only: the head's field `scope` fixes the layout file to that of the stored full-size
  example. The earlier hash `OnBytes.secondHashFunction` only, but for `p12_at_head`.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestKeepsFirst
import Johnson.IMR.LastFour
import Johnson.IMR.SendsFinal
import Johnson.Loose.H2K12.LaterSeatsN
import Johnson.P5J.AtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open VerifiableInference.Desc (Block Chain Place KindName)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}

/-- The flat list of the first chain has a block at number 354. -/
theorem member_at_354 (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∃ blk, cF.blocksInOrder[354]? = some blk := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, ⟨b, -, e, -⟩, -⟩ := IM.back_of O
  exact ⟨_, (IM.back_numbers h.scope h.reads O).1 1 b e⟩

/-- Its address: chain 1, in no link, piece 2, kind K12. By the proof it is one of the blocks after
the links (`cF.back`). -/
theorem place_at_354 (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[354]? = some blk) : blk.place = ⟨1, none, 2, .K12⟩ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, ⟨b, b', e, -, -, hla⟩, -⟩ := IM.back_of O
  obtain rfl := Option.some.inj (((IM.back_numbers h.scope h.reads O).1 1 b e).symm.trans hb)
  show b.place = _
  exact IM.alone_place hla

/-- Under the head a sample has one answer, at the parameters of the test at number 354. -/
theorem answers_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    (H2U.p12OfMade Zp.made).answers = 1 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact H2K.JointK.answers_of_planOk _
    (IM.hp_of_planOk h.scope h.reads O (IM.blocksOk_of_planOk O h.laid.planOk))

/-- The same parameters under the library's other name `pL Np`
(Johnson/Desc/K12/Law/SitsChains.lean). At every earlier hash `o`. -/
theorem p12_at_head {o : ProofFile.SecondHashFunctionArgument} (h : P5J.AtMg o Z D r Zp Np cF) :
    H2U.p12OfMade Zp.made = H2K.JointK.pL Np :=
  H2K.JointK.p12OfMade_is Zp Np h.laid.places

/-- **An accepting step of the block at number 354 gives `K12KeepsFirst`.** No hypothesis on the
state before the block. -/
theorem k12KeepsFirst_at_354 (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[354]? = some blk) (ft : Nat) (s s' : S) (hy : StepYes ft blk s s') :
    K12KeepsFirst (H2U.p12OfMade Zp.made) s s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨R, c, -, e⟩ := hy
  obtain ⟨⟨rs, gs, hd⟩, -, -⟩ := IM.at_354 h.scope h.reads O hb e
  exact k12KeepsFirst_of_yes _ (answers_at_head h) s s' rs gs hd

/-- **The kind and the clause at number 354, in one statement.** The hypothesis `s.failed = none`
is part of the form; the proof does not use it. At `ft = 0` only. -/
theorem k12Keeps_form_354 (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∀ blk, cF.blocksInOrder[354]? = some blk → blk.place.kind = KindName.K12 ∧
      ∀ s s', s.failed = none → StepYes 0 blk s s' →
        K12KeepsFirst (H2U.p12OfMade Zp.made) s s' := by
  intro blk hb
  refine ⟨?_, fun s s' _ hy => k12KeepsFirst_at_354 h hb 0 s s' hy⟩
  rw [place_at_354 h hb]

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.member_at_354
#print axioms ProofFile.Honest.Sh.place_at_354
#print axioms ProofFile.Honest.Sh.answers_at_head
#print axioms ProofFile.Honest.Sh.p12_at_head
#print axioms ProofFile.Honest.Sh.k12KeepsFirst_at_354
#print axioms ProofFile.Honest.Sh.k12Keeps_form_354
