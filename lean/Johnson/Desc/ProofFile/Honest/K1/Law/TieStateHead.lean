-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieStateHead.lean: TieStateS
(Johnson/Desc/ProofFile/Honest/K1/Law/TieShare.lean), THE PUBLIC HALF OF THE PREMISES OF THE SHARE
AT THE ITEM "tie m", AT THE OUTPUT HEAD's SEGMENT (m = 24): FROM THE MEMBER's OWN ACCEPT. One
statement and its proof. No definition.

  tieStateS_head   under four premises: which block the member is (hblk) and under which it lies
                   (hU) · which block its quiet half is (hquiet) · the plan's list of matrices has
                   the sizes' shapes (hShape):
                   TieStateS L Said b 24 nR at nR := the plan's number of reads

THE ROAD. The thread's step holds an accept of the member's decide (Block.step_ok,
Johnson/Desc/RunLaws.lean) at two rounds (roundsFit_len, Johnson/Desc/Sound/Gather.lean;
rounds_k1Reads, Johnson/Desc/K1/Law/BlocksAtLater.lean); the member is the sending joined with a
quiet block (joined_yes, Johnson/Desc/K1/Law/PubAtLaterIndex.lean); the quiet block's accept says
what it lays (head_ok, closed_ok: Johnson/Desc/K8/ReadsQuietLaws.lean): the link is opened; the
description's tables return t; the record behind is the plan's with its list closed at t's tables.
So its NM, mats and gtTree are the plan's, and the tables lie (tablesLie_head,
Johnson/HonestTrace/ReadsHead.lean).

Neither the pair in front nor the draws' fit is spent: the accept alone. No witness stands in it;
the run's coins stand as a binder of the threads' form alone.

THE MEMBER IS A LETTER (since […]). The blocks' class of claims Cl is a letter, and the
reads' member is a letter of the type Block S Cl, with ONE PUBLIC PREMISE: hU: it has the rounds of
the library's own block IM.k1Reads (Johnson/IMR/K1Seat.lean; typed there at Unit), carried to Cl by
Block.retype, and where it says yes that block says the same yes (Block.UnderR, step_under:
Johnson/Desc/Sound/SeatGuardChain.lean). WHY: the true chain's entry at a reads' place is not that
block: it is that block, retyped, under the seat's wrappers: k01_flat_reads
(Johnson/Desc/K1/Law/K01LawTied.lean), alone_underR (Johnson/IMR/SeatForm.lean): by these two hU is
meant to be paid there; NO FILE PAYS IT YET. Of the member the proof spends its rounds and its
decision's yes alone.

Limits. THE FOUR PREMISES ARE PROVED HERE AT NO LETTERS. hblk is an equation on the threads' letter
bs: the kind's record K1Seated has no such field: its fields on the member's decision see the
sending's half alone. hShape is a closed fact on a plan: it has been evaluated nowhere. At the
layers' segments the like wants one premise from the pair besides (what the state holds as heard is
a return of the layers' hearing); at the attention segments TablesLie is proved by nobody. Nothing
on soundness, on completeness or on any other property. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieShare
import Johnson.HonestTrace.ReadsHead
import Johnson.Desc.K1.Law.BlocksAtLater
import Johnson.Desc.K1.Law.PubAtLaterIndex
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.RunLaws
import Johnson.Desc.Sound.Gather
import Johnson.Desc.Sound.SeatGuardChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT roundsFit_len)
open VerifiableInference.Desc.K1 (joined_yes rounds_k1Reads)
open VerifiableInference.Desc.K8.ReadsQuiet (PH head head_ok closed_ok)
open OnBytes.HonestTrace (Sz ShapesFit shapesFit_congr tablesLie_head)
open OnBytes.Model.Stages (LinkH)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **The public half at the output head's segment, from the member's own accept.** -/
theorem tieStateS_head {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop} {b : ℕ} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {X : LinkH} {pr : ℕ} {reads : Option (List ℕ)} {Ph : PH}
    {blk₁ : Block S Cl} (hblk : L.bs[b]? = some blk₁)
    (hU : blk₁.UnderR ((IM.k1Reads Z G 24 X pr reads).retype : Block S Cl))
    (hquiet : IM.k1Quiet G 24 X = head Ph) (hShape : ShapesFit Ph.hp.tl Sz.ref 24) :
    TieStateS L Said b 24 (Ph.hp.nU.getD 2 0) := by
  intro blk hb k s μ E ds y cols s' _ _ hS
  obtain rfl : blk₁ = blk := Option.some.inj (hblk.symm.trans hb)
  unfold Thread.Stepped at hS
  obtain ⟨hfit, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS.2)
  have hlen : ((roundsOf y.1).map noDigest).length = 2 := by
    rw [List.length_map, roundsFit_len _ _ hfit]
    exact rounds_k1Reads Z G 24 X pr reads
  obtain ⟨r₁, r₂, hr⟩ := List.length_eq_two.1 hlen
  rw [hr] at hdec
  have hdec : (IM.k1Reads Z G 24 X pr reads).decide s [r₁, r₂] _ = .ok s' := hdec
  obtain ⟨s₁, gs₁, rs₂, gs₂, -, h3⟩ :=
    joined_yes _ _ _ _ _ (IM.k1Quiet G 24 X) s s' r₁ r₂ _ hdec
  rw [hquiet] at h3
  obtain ⟨a, cov, x, t, tl', -, hop, -, -, ht, hc, rfl⟩ := head_ok h3
  obtain ⟨-, rfl, -, -⟩ := closed_ok hc
  refine ⟨{ Ph.hp.tl with funClosed := true, funs := t.funs }, ?_,
    (shapesFit_congr ⟨rfl, rfl, rfl⟩ Sz.ref 24).2 hShape, tablesLie_head ht⟩
  show (if a.opened then some _ else none) = some _
  rw [if_pos hop]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tieStateS_head
