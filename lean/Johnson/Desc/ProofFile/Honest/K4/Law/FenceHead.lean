-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/FenceHead.lean: CONDITIONAL. One statement with its proof; no
definition.

What is here. `k4Fence_of_fold` (Law/FenceOfFold.lean (handed in with this file): five of the six
facts of `K4Fence`, Johnson/Road/K4/More/ElevenAtAll.lean, out of the library's facts on reached
states) AT THE LIBRARY's OWN CLOSED VALUES (`P5J.At.foldD`, `P5J.At.E`, and h.𝔇 of a hypothesis h :
AtMgA, the hypothesis on the public files): its seven equations hold by unfolding. K4 is the
sub-protocol of the feed-forward layers' own rounds.

  `k4Fence_head`   **`K4Fence h.𝔇 (P5J.At.E Zp cF L) m` of a reached state without a mark**, under
      h, F, hr, hm, hp, hl, h2 and heard.

Called. `k4Fence_of_fold`, with rfl at each of its seven equations.

Kin. As in Law/FenceOfFold.lean. `k4Fence_at` (Law/BehindHead.lean) calls this statement wherever
`lettersHead`'s thread stands, with F from `foldFacts_thr` (Honest/Thread/ReachFacts.lean, of other
writers); the proof of `front_three_head` (Law/FrontHead.lean) gives it heard from `k4_heard_head`
(Law/ReadyHead.lean): all six facts of `K4Fence` together, still under h and `LaidK4`.

Not shown here. As in Law/FenceOfFold.lean: `FoldFacts` (F) and heard are hypotheses. This file
gives no example of its hypotheses together (by binder, beside h: F, hr, hm, hp, hl, h2, heard);
where they are had: Kin. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one: its imports reach Johnson/Goal/. Following import lines, and
stopping unopened at every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/
and at every module whose name begins Cb.Bridge, its imports reach 17 modules under Johnson/Goal/
and 4 under Johnson/Bridge/, and none of the others; what lies behind the 21 is not counted; 46 of
the modules that it reaches have RecCompile in their names, none of them RecCompile's Honest*, Both
or PassH*. All these come with `K4Fence`'s file and with Johnson/P5J/MgAtAll.lean, which this file
imports for AtMgA. Earlier walks, which opened every module that they reached and read import lines
and nothing else, counted 47 under Johnson/Goal/, 48 with RecCompile in their names and 140 under
ThirdParty/; they are not made anew. No statement or proof of a file under Johnson/Goal/ or
ThirdParty/ was read for this file. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FenceOfFold
import Johnson.P5J.MgAtAll
import Johnson.P5J.WideAt
import Johnson.P5J.FoldAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Road.K4.More (K4Fence)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain)
open VerifiableInference.Desc.First (FoldFacts)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At the library's own closed values.** -/
theorem k4Fence_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Y : Type}
    {Rch : ℕ → Y → Prop} {at_ : Y → ProofFile.InstPub × TS}
    {L : VerifiableInference.Desc.K12.Door.Laid}
    (F : FoldFacts Rch at_ (P5J.At.foldD Zp cF L) P5J.At.reqW P5J.At.links P5J.At.ps) {k m : ℕ}
    {a : Y} {pl : Place} (hr : Rch k a) (hm : (at_ a).2.failed = none)
    (hp : P5J.At.ps[k]? = some pl) (hl : pl.link = some m) (h2 : 2 ≤ pl.piece)
    (heard : ∀ al fo', (at_ a).2.here = .lay al → al.fo = some fo' →
      fo'.shape = (P5J.At.X Zp).y.fo) :
    K4Fence h.𝔇 (P5J.At.E Zp cF L) m (at_ a).2 :=
  k4Fence_of_fold F rfl rfl rfl rfl rfl rfl rfl hr hm hp hl h2 heard

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Fence_head
