-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/LayersRecord.lean: WHAT THE STATE's RECORD OF THE SMALLNESS
TEST IS BEHIND THE READS' MEMBER OF A SEGMENT OF A GROUP OF LAYERS: FROM THE MEMBER's OWN ACCEPT:
THE PLAN's RECORD, CLOSED AT THE TABLES THAT THE STATE HOLDS AS ITS OWN HEARING's. The sister of
head_record (Johnson/Desc/ProofFile/Honest/K1/Law/HeadRecord.lean). Two statements and their proofs.
No definition. Public: no witness stands in it; the run's coins and the thread's middle stand as
binders of the step alone.

  layers_record   under which block the member's quiet half is (hquiet): behind the step, if the
                  state's record is tl: the state holds an own hearing "own" (s'.own? = some own);
                  tl.mats, tl.NM, tl.gtTree and tl.ix are the plan's; tl.funs = own.funs

THE ROAD is tieStateS_layers' (Johnson/Desc/ProofFile/Honest/K1/Law/TieStateLayers.lean):
Block.step_ok, joined_yes, layers_ok, closed_ok. That file keeps its own proof. Kin, not called:
quiet_layers_yes (Johnson/Meaning/QuietFront.lean): the last two in one, at the quiet block's own
decide.

WHAT IT IS FOR. tie_reads_layers (Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsLayers.lean) asks
hmats and hfuns. This pays hmats, and brings hfuns down to: the tables of the state's own hearing
are what funsOf returns at the filler's points.

THE MEMBER IS A LETTER (since […]). The blocks' class of claims Cl is a letter, and the
reads' member is a letter of the type Block S Cl, with ONE PUBLIC PREMISE: hU: it has the rounds of
the library's own block IM.k1Reads (Johnson/IMR/K1Seat.lean; typed there at Unit), carried to Cl by
Block.retype, and where it says yes that block says the same yes (Block.UnderR, step_under:
Johnson/Desc/Sound/SeatGuardChain.lean). WHY: the true chain's entry at a reads' place is not that
block: it is that block, retyped, under the seat's wrappers: k01_flat_reads
(Johnson/Desc/K1/Law/K01LawTied.lean), alone_underR (Johnson/IMR/SeatForm.lean): by these two hU is
meant to be paid there; NO FILE PAYS IT YET. Of the member the proof spends its rounds and its
decision's yes alone.

Limits. hquiet is proved here at no letters. Nothing ties own.funs to the filler's. Nothing on
soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieShare
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
open VerifiableInference.Desc.K8.ReadsQuiet (layers layers_ok closed_ok)
open OnBytes.Model (HTailF2)
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Model.Stages (LinkH)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **A block lies under itself retyped at its own class**: so at Cl := Unit and the written member
the premise hU of this file's law, and of those that call it, holds: the laws as they stood before
the member became a letter are corollaries. -/
theorem underR_retype_self {Cl : Type} (x : Block S Cl) : x.UnderR (x.retype : Block S Cl) :=
  ⟨rfl, fun _ _ _ _ h => h⟩

/-- **The state's record behind a layers' reads, from the member's own accept.** -/
theorem layers_record {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT} {m : ℕ}
    {Z : ProofFile.Pub} {G : ProofFile.Ground} {X : LinkH} {pr : ℕ} {reads : Option (List ℕ)} {hp : HPlan2}
    {pl : Place} (hquiet : IM.k1Quiet G m X = layers ⟨pl, hp.tl⟩) {k : Coins Bk} {s s' : S}
    {μ : Mid (Local W₀ Rc Xi Tr') X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr') X'} {cols : List OpenedColumn}
    {blk : Block S Cl}
    (hU : blk.UnderR ((IM.k1Reads Z G m X pr reads).retype : Block S Cl))
    (hS : L.thread.Stepped blk k s μ E ds y cols s') {tl : HTailF2}
    (htl : s'.tl? = some tl) :
    ∃ own, s'.own? = some own ∧ tl.mats = hp.tl.mats ∧ tl.NM = hp.tl.NM ∧
      tl.gtTree = hp.tl.gtTree ∧ tl.ix = hp.tl.ix ∧ tl.funs = own.funs := by
  unfold Thread.Stepped at hS
  obtain ⟨hfit, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS.2)
  have hlen : ((roundsOf y.1).map noDigest).length = 2 := by
    rw [List.length_map, roundsFit_len _ _ hfit]
    exact rounds_k1Reads Z G m X pr reads
  obtain ⟨r₁, r₂, hr⟩ := List.length_eq_two.1 hlen
  rw [hr] at hdec
  have hdec : (IM.k1Reads Z G m X pr reads).decide s [r₁, r₂] _ = .ok s' := hdec
  obtain ⟨s₁, gs₁, rs₂, gs₂, -, h3⟩ :=
    joined_yes _ _ _ _ _ (IM.k1Quiet G m X) s s' r₁ r₂ _ hdec
  rw [hquiet] at h3
  obtain ⟨a, own, tl', -, ho, hc, e⟩ := layers_ok h3
  obtain ⟨-, rfl, -, -⟩ := closed_ok hc
  have hown : s'.own? = some own := by
    rw [e]
    exact ho
  have e2 : some ({ hp.tl with funClosed := true, funs := own.funs } : HTailF2) = some tl := by
    rw [← htl, e]
    rfl
  obtain rfl := Option.some.inj e2
  exact ⟨own, hown, rfl, rfl, rfl, rfl, rfl⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.underR_retype_self
#print axioms ProofFile.Honest.K1.layers_record
