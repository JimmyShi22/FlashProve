-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04Counted.lean: THE KIND K4's OWN SENTENCE FOR THE JOIN, IN THE FORM IN WHICH A
KIND's LAW IS COUNTED: NAMED CONDITIONS → `AtMgA.Kind` (Johnson/P5J/RowsAtAll.lean) AT THE KIND K4.
One statement with its proof: two calls. IT PAYS NOTHING.

FIRST. NO FILE STATES A MEMBER OF `K4Cond` (K04Cond.lean). At some L it follows from the
head (`k4Cond_of_last`, K04Last.lean, at `k4Last_of_head`, K04OfHead.lean). K04_law IS NOT PROVED BY
THIS. A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/).

  `k04_counted`: `K4Cond hA L hA.toAtMg.typed` → for every 𝔏 with the three lists' heads: `hA.Kind 𝔏
    KindName.K4`: at the closed meaning `mgAtAll hA`, with "reached" and "the public part is a typed
    instance's" in hand.

HOW. `k04_of_cond_pub` at Pp := "the public part is a typed instance's" (`AtMg.typed`): its end is
`AtMgA.Kind`'s own text but for the spelling of the condition beside the promise (`AtMg.rch` is
`RchAt … ∧ typed …`, which is `RchPub`'s text): carried state by state through the tower's
`KindTiedR.mono`; `mgAtAll hA` is `mgAt … hA.𝔇` by unfolding. `K4Cond`'s three families along
"reached" stand at the same condition: at typed instances alone.

Limits. That file's. Nothing on soundness.
-/
import Johnson.Road.K4.K04Cond
import Johnson.P5J.RowsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop
open OnBytes OnBytes.Flat OnBytes.Maker KObj
open OnBytes.Model (Fork WsLay)
open OnBytes.Model.Verify (Public)
open VerifiableInference.OnPublicFiles (LeftQ)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Road.K4.InT (StatesAt)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block FileDescription KindName Wit Claim Link K9.LinkHoles K9.statesOfLink)
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf start openSets)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K13.Law (lowBits)
open Inst.Model (Scl ppref)
open Meaning.Emb (EmbNums)
open OnBytes.Model.Verify (layerShape)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.FFSeg (LW)
open Cb.Pv.Tail (Size)
open OnBytes.Model (Forest.elems)
open OnBytes.Desc.First.K4 (formsBack)
open VerifiableInference.PlanWritten (PublicSteps publicSteps_of)
open VerifiableInference.Desc.First (readsOpen moreItem)
open VerifiableInference.Desc.First.Look (pubAt stepOf)
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)
open VerifiableInference.Desc.K13.Law (matOfCells)

open OnBytes.Slice (frS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The IOP as written in Lean, at the head's letters. -/
local notation "𝐅" => (P5J.F0T OnBytes.secondHashFunction Zp Np cF)

/-- **K4's OWN SENTENCE, IN THE COUNTED FORM.** `K4Cond` IS SHOWN TO HOLD NOWHERE; UNDER THE HEAD
hA: A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/). -/
theorem k04_counted (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (L : VerifiableInference.Desc.K12.Door.Laid) (C : K4Cond hA L hA.toAtMg.typed)
    (𝔏 : P5J.Free numsFull D 𝐅 P5J.At.Tok)
    (q₁ : (𝐅).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (𝐅).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (𝐅).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) : P5J.AtMgA.Kind hA 𝔏 KindName.K4 :=
  KindTiedR.mono (fun _ _ h => ⟨h.1, h.2⟩) (k04_of_cond_pub hA L _ C 𝔏 q₁ q₂ q₃)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k04_counted
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
#check @OnBytes.Road.K4.k04_counted
