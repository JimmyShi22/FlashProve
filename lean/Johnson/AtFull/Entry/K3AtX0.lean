-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/K3AtX0.lean: the rows 11 and 12 of the proof file's entry tests
(`K3Asks.digEntry`, `readsEntry`: Johnson/Desc/First/Look/K3AsksDoor.lean) say yes at the three
full-size public files as Ladder/Stored.lean spells them (`VerifierAndGoals.storedPublicFiles`); row 13 (`headEntry`) does
under two equations on the head's lookup. Under the two closed facts on the layout file that
`madeAt_zFull` (Johnson/AtFull/Made/MadeAtZFull.lean) takes.
The letters. hsz: the layout file of `VerifierAndGoals.storedPublicFiles` has 224,975 bytes. b₁: it reads as the written
value `LW`. X₀: what `publicOfO OnBytes.secondHashFunction` returns at the three files (hX). m: what `Key.madeAt
X₀ storedPublicFiles.lay Key.fixedDigest` returns (hm). Zp: a public plan of the proof file whose planner's
structure is m with the segments' routines blanked (hZ : Zp.made = ProofFile.Law.blankM m).
  `facts_X0`: at X₀: profile 4, twelve groups, the head's shape is `Cond.hFull`, and the four tests
    of K3Places.lean say yes: by `at_witnesses` (Johnson/AtFull/Public/AtWitnesses.lean) from the
    closed facts K3DigL.lean, K3DigA.lean, K3DigH.lean, K3ReadsA.lean.
  `plan_of_made`: Zp.p.X = X₀, X₀'s frame is `Params.recordLines` (`PubFull.frame`), and
    `sentOf Zp = sentFull`: from the value that `madeAt_zFull`
    (Johnson/AtFull/Made/MadeAtZFull.lean) gives, by `sent_full`
    (Johnson/AtFull/ProofRows/K3Rows.lean).
  **`digEntry_zFull`** (k₁), **`readsEntry_zFull`** (k₂): no other premise: by `digEntry_full`,
    `readsEntry_full` (K3Rows.lean).
  `headEntry_zFull_of` (k₃): under hc : the head's six calls, their tables stripped, are
    `callsHead`, and hp : the lookup's numbers of padding keys are `pubHead`
    (Johnson/AtFull/ProofRows/K3HeadRow.lean). Paid here: the place is there; its lid is 28; the
    eleven numbers of the head's shape; the kind's own test on the calls (`place_calls_ok`,
    Johnson/AtFull/ProofRows/K3CallsOkHead.lean).
Limits. UNDER hsz AND b₁, WHICH ARE NOT PAID HERE (they are shown in the side library:
AtFullSide/Layout/Size.lean, AtFullSide/LayoutRead/Full.lean). ROW 13 KEEPS TWO PREMISES. At
`VerifierAndGoals.storedPublicFiles` alone: three terms written in Ladder/Stored.lean; no Lean code ties them to the
top-level folder examples/. At the second hash function and the constant digest. A yes of tests on
public data: no proof is read, and nothing is accepted. Nothing on soundness, on a binding of the
commitment (the opening form, `BindsWith`), on correctness of extraction, on completeness or on
hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.AtFull.Entry.K3DigL
import Johnson.AtFull.Entry.K3DigA
import Johnson.AtFull.Entry.K3DigH
import Johnson.AtFull.Entry.K3ReadsA
import Johnson.AtFull.ProofRows.K3Rows
import Johnson.AtFull.ProofRows.K3CallsOkHead
import Johnson.AtFull.Made.MadeAtZFull
import Johnson.Desc.ProofFile.Law.PlainIsMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Entry
open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Public (Makers at_witnesses opens_yFull)
open OnBytes.Road.K4.Trial.Values (yFull polLayout_W)
open OnBytes.Model.Layer (ropeTable)
open VerifiableInference.PlanWritten (publicOfO publicOfO_older)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open VerifiableInference.Desc.K3Asks
open VerifiableInference.Desc.First.Look (lookAt)
open Johnson.AtFull.LayoutRead (LW)
open Johnson.AtFull.ProofRows.K3
open VerifiableInference.Desc.Kinds.Head.Law (Cond.hFull)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (shape_at_stored)

/-- At the public part's value: profile 4, twelve groups, the head's shape, and the four tests. -/
theorem facts_X0 (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) :
    X₀.p4 = true ∧ X₀.NGr = 12 ∧ X₀.hS = Cond.hFull ∧ digLB X₀.G = true ∧ digAB X₀.A = true ∧
      digHB X₀.H X₀.layers.wsLay.lk = true ∧ readsAB X₀.A = true := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e1, e2, -, e4, ⟨e5, -⟩, e6, e7, e8, -, -,
    hX'⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  obtain ⟨pp, hF, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨-, -, -, p10, -⟩ := Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hF polLayout_W
  have M : Makers yFull sc wsLay (ropeTable 12 500000 128 10) l ps layers G seenA :=
    { groups := _root_.AtFull.Public.yFull_NGr, p3 := _root_.AtFull.Public.yFull_p3,
      p4 := _root_.AtFull.Public.yFull_p4, scales := e1, weights := e2, rotary := p10, lines := e4,
      twins := e5, record := e6, plans := e7, owners := e8 }
  have ey : layers.y = yFull := OnBytes.Road.Hd.pubOf_y e6
  have e : X₀ = _ := Except.ok.inj (hX.symm.trans hX')
  rw [e]
  refine ⟨?_, ?_, ?_, at_witnesses opens_yFull M digL_W, at_witnesses opens_yFull M digA_W,
    at_witnesses opens_yFull M digH_W, at_witnesses opens_yFull M readsA_W⟩
  · show layers.y.h.p4 = true
    rw [ey]
    exact _root_.AtFull.Public.yFull_p4
  · show layers.y.NGr = 12
    rw [ey]
    exact _root_.AtFull.Public.yFull_NGr
  · show headShape (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef VerifierAndGoals.storedLines) yFull =
      Cond.hFull
    rw [shape_at_stored, _root_.AtFull.Public.yFull_lPd]
    rfl

/-- The public plan's public part is X₀, its frame is the written one, and what the tests read
beside it is the written value. -/
theorem plan_of_made (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (b₁ : Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay = some LW) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ VerifierAndGoals.storedPublicFiles.lay fixedDigest = .ok m)
    {Zp : ProofFile.Pub} (hZ : Zp.made = ProofFile.Law.blankM m) :
    Zp.p.X = X₀ ∧ X₀.P.frame = Params.recordLines ∧ sentOf Zp = sentFull := by
  obtain ⟨X₁, links₀, links, sh, hX₁, hm₁, -, -, hv, -, -, fw, -, P, -, -⟩ :=
    Johnson.AtFull.Made.madeAt_zFull hsz b₁
  obtain rfl : X₁ = X₀ := Except.ok.inj (hX₁.symm.trans hX)
  obtain rfl : _ = m := Except.ok.inj (hm₁.symm.trans hm)
  have hp : Zp.p = (ProofFile.Law.blankM _).p := congrArg (·.p) hZ
  refine ⟨by rw [hp]; rfl, P.frame, ?_⟩
  obtain ⟨c1, -, c3, -, -, c6⟩ := fw
  refine sent_full ?_ ?_ ?_ ?_
  · show Zp.p.chains.proof.first.codes = _
    rw [hp]
    exact c1
  · show Zp.p.chains.proof.first.shape = _
    rw [hp]
    exact c3
  · show Zp.p.chains.proof.first.layout = _
    rw [hp]
    exact c6
  · rw [hp]
    show (links.map ProofFile.Law.blank).toList.map Johnson.AtFull.Made.viewOf = _
    rw [Array.toList_map, List.map_map]
    exact hv

section
variable (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (b₁ : Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay = some LW)
  {X₀ : Public}
  (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
  {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ VerifierAndGoals.storedPublicFiles.lay fixedDigest = .ok m)
  {Zp : ProofFile.Pub} (hZ : Zp.made = ProofFile.Law.blankM m)
include hsz b₁ hX hm hZ

/-- **k₁: the entry test on the digits says yes.** -/
theorem digEntry_zFull : digEntry Zp = true := by
  obtain ⟨h4, hN, -, hL, hA, hH, -⟩ := facts_X0 hsz hX
  obtain ⟨eX, hF, hD⟩ := plan_of_made hsz b₁ hX hm hZ
  refine digEntry_full ?_ ?_ ?_ hD ?_
  · rw [eX]
    exact h4
  · rw [eX]
    exact hN
  · rw [eX]
    exact hF
  · rw [eX]
    exact dig_gives h4 hN hL hA hH

/-- **k₂: the entry test on the guards of attention's callers' reading says yes.** -/
theorem readsEntry_zFull : readsEntry Zp = true := by
  obtain ⟨h4, hN, -, -, -, -, hR⟩ := facts_X0 hsz hX
  obtain ⟨eX, -, hD⟩ := plan_of_made hsz b₁ hX hm hZ
  refine readsEntry_full ?_ ?_ hD ?_
  · rw [eX]
    exact h4
  · rw [eX]
    exact hN
  · rw [eX]
    exact reads_gives h4 hR

/-- k₃: the entry test on the output head's calls says yes, under two equations on the head's
lookup. -/
theorem headEntry_zFull_of (hc : X₀.HLy.cl.map strip = callsHead)
    (hp : X₀.HLy.fs.pub = pubHead) : headEntry Zp = true := by
  obtain ⟨h4, hN, hS, -, -, -, -⟩ := facts_X0 hsz hX
  obtain ⟨eX, -, -⟩ := plan_of_made hsz b₁ hX hm hZ
  have hx : ∃ x, lookAt X₀ 24 false = some x ∧ x.calls = X₀.HLy.cl ∧ x.pub = X₀.HLy.fs.pub ∧
      x.lid = X₀.hS.LIDB := by
    unfold lookAt
    simp only [h4, hN, if_true]
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  obtain ⟨x, ex, xc, xp, xl⟩ := hx
  have hO : publicOf VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ := by
    rw [← publicOfO_older]
    exact hX
  refine headEntry_full (x := x) ?_ ?_ ?_ (place_calls_ok hO h4 hN ex) ?_ ?_ ?_ ?_
  · rw [eX]
    exact h4
  · rw [eX]
    exact hN
  · rw [eX]
    exact ex
  · rw [xc]
    exact hc
  · rw [xl, hS]
    rfl
  · rw [xp]
    exact hp
  · rw [eX, hS]
    rfl

end

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.facts_X0
#print axioms Johnson.AtFull.Entry.plan_of_made
#print axioms Johnson.AtFull.Entry.digEntry_zFull
#print axioms Johnson.AtFull.Entry.readsEntry_zFull
#print axioms Johnson.AtFull.Entry.headEntry_zFull_of
