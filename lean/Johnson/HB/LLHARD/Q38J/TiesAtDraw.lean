-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38J/TiesAtDraw.lean: four ties for `DigAheadOk` behind the approximate range
proof's draw: the composed meaning's letters at the head, and what the state in front of the draw
holds.

Why. `DigAheadOk` (Johnson/Desc/First/Look/K3DigitsAhead.lean) speaks at the letters of the composed
meaning (`h.𝔇.sent`, `h.𝔇.l3.seat`, `h.𝔇.N`). The laws on reached states speak at the closed letters
(`P5J.At.sentAt Zp`, `P5J.At.foldD Zp cF L₀`). The first lemma states that the two writings are one;
the joins of this family go by unfolding and do not call it. The others read three of the clauses on
the state off the ground and off the facts on every reached state (`FoldFacts`).

What is shown.
  `letters_at_head`: the four letters are the closed ones: by unfolding.
  `arr_at`: the built segment's list of arrays is what the planner sends at that segment.
  `frameIs_at_draw`: **at a reached state without a mark in front of the draw of segment l, the open
    segment's frame has the four facts `FrameIs`.** By `FoldFacts.liveShape`, `liveGroups`,
    `frameIs` at the place that the written list of places has at the draw's number
    (`draw_place_full`).
  `codes_at_draw`: the statement's codes there are the planner's.

Grade. No field of the head is read, and no entry test is spent: `letters_at_head` is by unfolding;
`arr_at` takes the ground; the two others take `FoldFacts` as a premise: the rows that its payer
spends are not counted here.

Limits. No state is shown at which the premises hold. The full size alone. Nothing on soundness.


-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.FoldAt
import Johnson.P1K8R.SmallAtHead
import Johnson.IMR.ArraysOpen
import Johnson.Desc.First.Att.K05SeatsOne
import Johnson.Desc.First.Link.Law.PartFitsReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Q38

open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S FoldFacts)
open VerifiableInference.Desc.First.K8 (drawAt)
open VerifiableInference.Desc.First.Att.P (FrameIs born_of_groups)
open ProofFile (Cl)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- The composed meaning's four letters are the closed ones. -/
theorem letters_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (L₀ : VerifiableInference.Desc.K12.Door.Laid) :
    h.𝔇.sent = P5J.At.sentAt Zp ∧ (P5J.At.foldD Zp cF L₀).sent = P5J.At.sentAt Zp ∧
      h.𝔇.l3.seat = P5J.At.seat3At Zp ∧ h.𝔇.N = P5J.At.N Zp cF :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The built segment's list of arrays is what the planner sends there. -/
theorem arr_at {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ}
    {Xl : LinkH} (e3 : G.built[l]? = some Xl) :
    Xl.arrayOf = (P5J.At.sentAt Zp).arrayOf.getD l #[] :=
  Meaning.K2.built_arr hG e3

/-- **The frame's four facts in front of the draw.** -/
theorem frameIs_at_draw {Str : Type} {Rch : ℕ → (ProofFile.InstPub × S) × Str → Prop}
    {L₀ : VerifiableInference.Desc.K12.Door.Laid}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF L₀) P5J.At.reqW P5J.At.links P5J.At.ps)
    {l : ℕ} {a : (ProofFile.InstPub × S) × Str} (hr : Rch (drawAt l) a) (hu : a.1.2.failed = none)
    {L : LinkCtx} (hL : a.1.2.link? = some L) (hl : l ≤ 24) :
    FrameIs (P5J.At.sentAt Zp) l L.check.frame := by
  obtain ⟨p, hp, hlk, hpc, -⟩ := P1K8T.draw_place_full l hl
  obtain ⟨-, -, -, h4⟩ := FF.frameIs (drawAt l) a p l L hr hu hp hlk hL
  obtain ⟨e1, e2⟩ := h4 hpc
  have hs := FF.liveShape (drawAt l) a hr hu
  have hg := FF.liveGroups (drawAt l) a hr hu
  rw [VerifiableInference.Desc.LinkJoin.live_link hL] at hs hg
  exact ⟨hs, born_of_groups (by rw [hg, hs]; rfl) e1, e1, e2⟩

/-- The statement's codes in front of the draw. -/
theorem codes_at_draw {Str : Type} {Rch : ℕ → (ProofFile.InstPub × S) × Str → Prop}
    {L₀ : VerifiableInference.Desc.K12.Door.Laid}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF L₀) P5J.At.reqW P5J.At.links P5J.At.ps)
    {l : ℕ} {a : (ProofFile.InstPub × S) × Str} (hr : Rch (drawAt l) a) (hu : a.1.2.failed = none) :
    a.1.2.st.codes = (P5J.At.sentAt Zp).codes :=
  FF.codes (drawAt l) a hr hu

end Q38

#print axioms Q38.letters_at_head
#print axioms Q38.arr_at
#print axioms Q38.frameIs_at_draw
#print axioms Q38.codes_at_draw
