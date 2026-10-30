-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/FenceOfFold.lean: CONDITIONAL. One statement with its proof; no
definition.

What is here. FIVE OF THE SIX FACTS OF `K4Fence` (Johnson/Road/K4/More/ElevenAtAll.lean: what the
library's law on the public tests behind K4, the sub-protocol of the feed-forward layers' own
rounds, asks of the state in front, beside the promise) OUT OF THE LIBRARY's FACTS ON REACHED STATES
(`FoldFacts`, Johnson/Desc/First/FoldFacts.lean). General in the data: the two structures' data, the
condition Rch and the map at_ are letters.

  `k4Fence_of_fold`   under F : `FoldFacts`; SEVEN EQUATIONS between the two structures' public
      numbers (eL, eM, e0, ef, es, ey, ec); FIVE PREMISES ON THE STATEMENT a AND ITS STATE: a is
      reached at border k (hr) · its state bears no mark (hm) · the place at k (hp) · that place's
      segment (hl) · its piece is at least 2 (h2); and heard.

Called. Six fields of `FoldFacts`: room, liveShape, liveLayout, seatsCarried, msgShapes, codes. The
proof is these projections and rewriting by the equations.

Kin. Other writers draw what their own sub-protocols' laws ask out of `FoldFacts` in the like way:
`foldAt_of_facts` (Johnson/Desc/Kinds/Law/K6RestOfFold.lean) spends five of these six fields, all
but room; `factsK13_of_fold` (Johnson/Desc/K13/Law/FactsOfFold.lean) spends twelve, three of these
six among them (seatsCarried, msgShapes, codes). Neither ends in `K4Fence`. `k4Fence_head`
(Law/FenceHead.lean (handed in with this file)) is this statement at the library's own closed
values.

Not shown here. THAT `FoldFacts` HOLDS ANYWHERE: F is a hypothesis. THE SIXTH FACT (heard: what the
lookup heard has the public parameters' shape) IS A HYPOTHESIS TOO: no field of `FoldFacts` says it.
This file gives no example of its hypotheses together. WHERE THEY ARE HAD: at `lettersHead`'s
thread, under h : AtMgA, the hypothesis on the public files. `foldFacts_thr`
(Honest/Thread/ReachFacts.lean, of other writers) ends in `FoldFacts` at «the thread stands here»,
and `k4Fence_at` (Law/BehindHead.lean) calls `k4Fence_head` with it; `k4_heard_head`
(Law/ReadyHead.lean) has heard wherever that thread stands in front of K4's member, under four
hypotheses more (hH, AtK4, K4OnX, K4OnD); the proof of `front_three_head` (Law/FrontHead.lean) lays
the one into the other: all six facts together, still under h and `LaidK4`. `heard_shape_layers`
(Honest/K3/Law/Thread/PutFo.lean, of other writers) has heard's sentence of the state right behind
the accepting step of the lookup's member, under hypotheses of its own. A LAW, NOT A PART: no file
that defines a part of the proof file's description may import this one: its imports reach
Johnson/Goal/. Following import lines, and stopping unopened at every module under Johnson/Goal/,
Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name begins Cb.Bridge, its
imports reach 4 modules under Johnson/Goal/ and 2 under Johnson/Bridge/, and none of the others;
what lies behind the six is not counted; 29 of the modules that it reaches have RecCompile in their
names. All these come with the file that defines `K4Fence`. An earlier walk, which opened every
module that it reached and read import lines and nothing else, counted 21 under Johnson/Goal/; it is
not made anew. No statement or proof of a file under Johnson/Goal/ was read for this file. Nothing
on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Road.K4.More.ElevenAtAll
import Johnson.Desc.First.FoldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Road.K4.More (K4Fence)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart FoldFacts FoldData)
open VerifiableInference.Desc.First.Look (liveIsB)
open VerifiableInference.Desc.Sound (MgData WideData)

/-- **Five of the six out of the facts on reached states; the sixth asked.** -/
theorem k4Fence_of_fold {Xi P Tok Y : Type} {rows cols nR : ℕ} {X : Verify.Public}
    {Dm : MgData Xi P Tok rows cols nR X} {E : WideData P} {Rch : ℕ → Y → Prop}
    {at_ : Y → P × S} {d : FoldData} {reqW : P → Array UInt32} {links : List ModelPart}
    {ps : List Place} (F : FoldFacts Rch at_ d reqW links ps) (eL : E.d12.L = d.L)
    (eM : E.d12.M = d.M) (e0 : E.dP.free0 = d.free0) (ef : E.dP.fvs = d.fvs)
    (es : Dm.sent.shape = d.sent.shape) (ey : Dm.sent.layout = d.sent.layout)
    (ec : Dm.cs = d.sent.codes) {k m : ℕ} {a : Y} {pl : Place} (hr : Rch k a)
    (hm : (at_ a).2.failed = none) (hp : ps[k]? = some pl) (hl : pl.link = some m)
    (h2 : 2 ≤ pl.piece)
    (heard : ∀ al fo', (at_ a).2.here = .lay al → al.fo = some fo' → fo'.shape = X.y.fo) :
    K4Fence Dm E m (at_ a).2 :=
  { room := by
      rw [e0, ef]
      exact F.room k a pl m hr hm hp hl h2
    live := by
      unfold liveIsB
      rw [es, ey, F.liveShape k a hr hm, F.liveLayout k a hr hm]
      simp
    seats := by
      rw [eL]
      exact F.seatsCarried k a hr hm
    shapes := by
      rw [eM]
      exact F.msgShapes k a hr hm
    codes := by
      rw [ec]
      exact F.codes k a hr hm
    heard := heard }

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Fence_of_fold
