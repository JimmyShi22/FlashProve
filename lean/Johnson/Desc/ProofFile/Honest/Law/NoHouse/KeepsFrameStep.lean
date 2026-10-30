-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/KeepsFrameStep.lean: the clause `keepsFrame`
(KeepsFrame.lean) at the 77 sub-protocols of the kind `frame` of the first chain at the full size,
from the sub-protocol's accepting step (`StepYes`, Johnson/Top/H0/Walk/Reach.lean). Each lemma
speaks of a sub-protocol by its number in the chain's flat list. It says that the place there is of
the kind `frame`, and that an accepting step from `s` to `s'` gives the clause at that place. This
is the form in which the column for `keeps` of the first chain's invariant is gathered number by
number (Thread/SteppedYes.lean, Thread/Numbers358.lean). No definition.

  1  `frame_keeps_front`, `front_accepts_any`   number 0
  2  `frame_keeps_laid`      numbers `14 * l + 1`, the frame's step "laid" of segment `l`
  3  `frame_keeps_behind`    numbers `14 * l + IM.nAt l + 3`, the frame's step after the batching
  4  `frame_keeps_cleared`   numbers `14 * l + IM.nAt l + 7`, the frame's step "cleared"
  5  `frame_keeps_seal`      number 357, the chain's end

Which sub-protocol is at a number is the library's: `IM.front_of` (Johnson/IMR/FrontSeat.lean),
`IM.frame_of` (Johnson/IMR/FrameSeat.lean), `P5J.sits_at` (Johnson/P5J/K09List.lean) with
`LPFK9.batch_nAt` (Johnson/LPFK9R/HtinAtConstant.lean), and `IM.back_numbers` with
`IM.seal_seated` through `head_seat357` and `head_sealed` (Seal.lean). An accepting step is an
accepting decision by the library's `stepYes_decide` (Johnson/Top/H0/Walk/ReachInv.lean). The clause
then follows by `kp_out`, `kp_laid`, `kp_cleared` (KeepsFrameAt.lean) and `after_keeps`
(BehindShare.lean).

Two of the five families take one hypothesis more. Every arm of `keepsFrame` contains "no mark of
failure after the step". At "laid", at "cleared" and at the chain's end the sub-protocol as the
chain holds it tests the mark, so its accepting step gives that. The sub-protocol at number 0 and
the 25 steps after a batching do not test the mark. `front_accepts_any` shows that the one at number
0 accepts at every state and returns it, so at a state with a mark the clause does not follow
there. `frame_keeps_front` and `frame_keeps_behind` therefore take "no mark of failure before the
step" as a hypothesis. The invariant has it at every border.

Limits.
  * That a `StepYes` exists at any state is shown at number 0 only.
  * At "cleared" the argument `take` of the clause is the library's `P1L20.bearing`.
  * Whether a step after a batching accepts at some state with a mark is not shown.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.KeepsFrameAt
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Seal
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindAll
import Johnson.Top.H0.Walk.ReachInv
import Johnson.Top.H0.Walk.FrameProps
import Johnson.LPFK9R.HtinAtConstant
import Johnson.IMR.FrontSeat
import Johnson.IMR.FrameSeat
import Johnson.IMR.PlacesScope
import Johnson.P1L20R.FrameNoneAt
import Johnson.P5J.K09List

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName Block step_iff)
open VerifiableInference.Desc.LinkJoin (hearN)
open Johnson.Desc.First.Walk.Props (layFront_iff)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (take : Nat → Bool)

include h

/-! ## 1 Number 0 -/

/-- At number 0, from a state without a mark of failure. -/
theorem frame_keeps_front :
    ∀ blk, cF.blocksInOrder[0]? = some blk → blk.place.kind = KindName.frame ∧
      ∀ s s', s.failed = none → StepYes 0 blk s s' →
        keepsFrame P5J.At.links take blk.place s s' := by
  intro blk hb
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b0, e0, -, -, hpl, -, hd⟩ := IM.front_of O
  obtain rfl : blk = b0 := Option.some.inj (hb.symm.trans e0)
  refine ⟨by rw [hpl], fun s s' h0 hy => ?_⟩
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  have es : s' = s := (hd s rs gs s').1 e
  subst es
  rw [hpl]
  exact kp_out P5J.At.links take (p := ⟨1, none, 0, KindName.frame⟩) rfl _ h0

/-- The sub-protocol at number 0 accepts at every state, with a mark of failure or without, and
returns the state. So the hypothesis on the mark in `frame_keeps_front` cannot be dropped. -/
theorem front_accepts_any : ∀ blk, cF.blocksInOrder[0]? = some blk → ∀ s, StepYes 0 blk s s := by
  intro blk hb s
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b0, e0, hr, -, -, -, hd⟩ := IM.front_of O
  obtain rfl : blk = b0 := Option.some.inj (hb.symm.trans e0)
  have hw : blk.want 0 [] = [] := by
    unfold VerifiableInference.Desc.Block.want
    rw [hr]
    rfl
  refine ⟨[], [], (congrArg List.length hr).symm,
    (step_iff 0 blk s s [] [] 0).2 ⟨⟨?_, ?_⟩, (hd s _ _ s).2 rfl, ?_⟩⟩
  · exact (congrArg (fun l => VerifiableInference.Desc.roundsFit l []) hr).trans rfl
  · rw [hw]
    rfl
  · rw [hw]
    rfl

/-! ## 2 "Laid" -/

/-- At the frame's step "laid" of segment `l`. -/
theorem frame_keeps_laid {l : Nat} (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[14 * l + 1]? = some blk → blk.place.kind = KindName.frame ∧
      ∀ s s', StepYes 0 blk s s' → keepsFrame P5J.At.links take blk.place s s' := by
  intro blk hb
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, -, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, f, bL, bB, bC, -, -, -, -, hlayf, hLay, -, iL, -, dL, -⟩ := hall l hl
  obtain rfl : blk = bL := Option.some.inj (hb.symm.trans iL)
  obtain ⟨hp, -⟩ := P1L20.places_full hl
  have hpl : blk.place = ⟨1, some l, 0, KindName.frame⟩ := by
    have e := IM.place_at h.scope h.reads O hb
    rw [P1L20.placesW_eq, hp] at e
    exact (Option.some.inj e).symm
  refine ⟨by rw [hpl], fun s s' hy => ?_⟩
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  rw [dL, hLay, hlayf, layFront_iff] at e
  obtain ⟨⟨es, -⟩, h0, -⟩ := e
  subst es
  rw [hpl]
  exact kp_laid P5J.At.links take (p := ⟨1, some l, 0, KindName.frame⟩) rfl rfl _ h0

/-! ## 3 After the batching -/

/-- At the frame's step after the batching of segment `l`, from a state without a mark of failure.
-/
theorem frame_keeps_behind {l : Nat} (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk → blk.place.kind = KindName.frame ∧
      ∀ s s', s.failed = none → StepYes 0 blk s s' →
        keepsFrame P5J.At.links take blk.place s s' := by
  intro blk hb
  obtain ⟨Lk, p9, Q9, b₃, b₅, St⟩ := P5J.sits_at h l hl
  have hs := behind_seat h St
  rw [LPFK9.batch_nAt l hl] at hs
  obtain rfl : blk = Lk.behindB := Option.some.inj (hb.symm.trans hs)
  refine ⟨rfl, fun s s' h0 hy => ?_⟩
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  refine (keepsFrame_behind P5J.At.links take (l := l) ?_ ?_ s s').2
    (after_keeps Lk (after_share_head h hl St.lk St.seg) s s'
      (rows_share_head h hl St.lk St.seg) h0 e)
  · show some Lk.number = some l
    rw [behind_num_head h hl St.lk]
  · show Lk.hear.length + 2 = hearN fullLinks l + 2
    unfold hearN
    rw [St.sort, St.seg.hear]
    rfl

/-! ## 4 "Cleared" -/

/-- At the frame's step "cleared" of segment `l`. The argument `take` of the clause is the library's
`P1L20.bearing`: segment `l` leaves a pending row. -/
theorem frame_keeps_cleared {l : Nat} (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 7]? = some blk → blk.place.kind = KindName.frame ∧
      ∀ s s', StepYes 0 blk s s' → keepsFrame P5J.At.links P1L20.bearing blk.place s s' := by
  intro blk hb
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, f, bL, bB, bC, -, hn, hf, -, -, -, hClear, -, -, -, -, -, -, iC, -, dC⟩ :=
    hall l hl
  rw [hn] at iC
  have hb' : cF.blocksInOrder[P1L20.clearIx l]? = some blk := hb
  obtain rfl : blk = bC := Option.some.inj (hb'.symm.trans iC)
  obtain ⟨-, -, -, hp, -⟩ := P1L20.places_full hl
  have hpl : blk.place = P1L20.clearPlace l := by
    have e := IM.place_at h.scope h.reads O hb'
    rw [P1L20.placesW_eq] at e
    exact Option.some.inj (e.symm.trans hp)
  refine ⟨by rw [hpl], fun s s' hy => ?_⟩
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  rw [dC, hClear] at e
  rw [hpl]
  exact kp_cleared h P5J.At.links hl hfs hf s s' e.1 e.2.1

/-! ## 5 The chain's end -/

/-- At the chain's end, number 357. -/
theorem frame_keeps_seal :
    ∀ blk, cF.blocksInOrder[357]? = some blk → blk.place.kind = KindName.frame ∧
      ∀ s s', StepYes 0 blk s s' → keepsFrame P5J.At.links take blk.place s s' := by
  intro blk hb
  have hla := head_sealed h
  have hk7 : ({ chain := 1, link := none, piece := 5, kind := .frame } : Place).kind ≠
      KindName.K7 := by decide
  have eb : blk = { cF.last with planOk := cF.last.planOk && cF.last.hasNoClaimsAndNothingAfter } :=
    Option.some.inj (hb.symm.trans (head_seat357 h))
  have hpl : blk.place = ⟨1, none, 5, KindName.frame⟩ := by
    rw [eb]
    show cF.last.place = _
    exact IM.alone_place hla
  refine ⟨by rw [hpl], fun s s' hy => ?_⟩
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  rw [eb] at e
  have e' : cF.last.decide s rs gs = .ok s' := e
  obtain ⟨-, h0, es⟩ := (seal_decide hla hk7 s s' rs gs).1 e'
  subst es
  rw [hpl]
  exact kp_out P5J.At.links take (p := ⟨1, none, 5, KindName.frame⟩) rfl _ h0

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.frame_keeps_front
#print axioms ProofFile.Honest.FirstThread.front_accepts_any
#print axioms ProofFile.Honest.FirstThread.frame_keeps_laid
#print axioms ProofFile.Honest.FirstThread.frame_keeps_behind
#print axioms ProofFile.Honest.FirstThread.frame_keeps_cleared
#print axioms ProofFile.Honest.FirstThread.frame_keeps_seal
