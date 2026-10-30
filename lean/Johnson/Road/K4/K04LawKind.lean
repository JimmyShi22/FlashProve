-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04LawKind.lean: the kind K4's share of the chain of promises in the form in which a
kind's law is to end: `AtMg.Kind` (Johnson/P5J/RowsAtMg.lean), under the one head, at the closed
constant. One statement with its proof: `k04_law_front`
(K04LawFront.lean) called at the head's own terms. No new argument. It pays nothing of weight.

First. No member of its binders is shown anywhere. Under the binders of `k04_of_head`
(Johnson/Road/K4/K04OfHead.lean: the head, a filling 𝔏, three equations on the flat lists) they are
had: that theorem reaches this statement by calls; a member of the head is proved at `storedPublicFiles` and
`zGap` alone (at secondHashFunction, with `fixedConfigurationDigest` in the digest's place; side library AtFullSide/Top/). K04_law
is not proved by this. One of the constant's terms (cr1) is not final: rest on it at no
border in front of the shutting. What this calls speaks at the wider meaning, one side of a bridge:
what the bridge spends is a binder here (W0, R0, L7).

  `k04_kind`: for hA : `AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀` and every condition Pp on the public
    part: `KindTiedR (At.N Zp cF) (mgAt … hA.𝔇) fullLinks At.ps (RchPub (F0T …) Pp) (h.ex 𝔏) (h.row
    𝔏) KindName.K4`: `AtMg.Kind`'s own text but for the condition beside the promise: "reached, and
    Pp of the public part" (`RchPub`, Johnson/Top/H0/Walk/ReachPub.lean). At Pp := "true" it gives
    `AtMg.Kind`; at "the public part is a typed instance's" the counted form: that half is
    K04Counted.lean's. (Where this and lean/THEOREM.md differ, the page holds.)


At the second hash function alone (o := `OnBytes.secondHashFunction`), where the counted laws are owed. At the
closed structure of data alone (𝔇₀ := `hA.𝔇`, every field a term), not at every 𝔇₀: the equations
that K4's payers ask touch six fields that the head's own filling leaves to 𝔇₀ (d1, headPart, P13,
mat13, uL, seat3). "Reached" is the fixed term `RchAt` of the IOP as written in Lean, no letter; Pp
beside it is a letter, and the same Pp stands in the premises W0, R0, L7: so these are asked at no
more states than the end speaks of.

What the head gives, by calls. The scope and the reading of the files: its fields. `T` := the
maker's own three rows, with "T holds the IOP's sub-protocols", the cut and the cap:
`AtMg.pieces` (Johnson/Road/K4/RowAtMg.lean). The data: `LaidAt.data`, at the frame's depth of the
committed table (`LaidAt.atDepth`). `sealLast` and `blocksOk`: two parts of `LaidAt.planOk`
(`planOk_parts`). The table's extractor lays nothing at K4's twelve numbers: `AtMg.ex_quiet`. The
public parameters: the opening's own equation (`Open.W`). The number of the pile's rows: the
constant lays it. The pile's columns (hkC): the head's field cols13: so it
is no theorem. "The output head's segment is no feed-forward segment":
in scope that segment has the number 24 (`headLink_in_scope`), and the constant's list of segments
is the written one, at which the test is decided. `K4Fill` (twelve lines):
`k4Fill_all`: from the head alone. The families `K4LaterAt` and `K4FirstAt`: two
joins (in K04LawFull.lean). What the bridge spends behind K4: `sp_of_front_pub` (in
K04LawFront.lean).

What stays. O: an opening: `LaidAt.opened` says that there is one; it is a binder because the
families below speak of its base · q₁ q₂ q₃: the three lists' heads (the rule that spends the laws
takes them too) · L: the listed seats and trees' shapes of the chain: a letter: the struck parts'
data are the term `eAll Zp cF L` over it · Pf: eight named equations and one line on
the constant · reqT: three lines on the request's readers (both paid in K04Cond.lean, by calls) ·
Sn, hNf, Pt: tests · W: five equations: the public part's plan is the written one · W0, R0, L7: at
the twelve borders in front of K4, at every state that the IOP's run reaches there without a mark
and whose public part meets Pp: the fifteen facts (`WideFacts`), the room's test, the seven fields'
test · lw (idle).

Limits. Every binder is a premise. Shown together at no data. The full size alone. Nothing on
soundness.
-/
import Johnson.Road.K4.K04LawFront
import Johnson.Road.K4.RowAtMg
import Johnson.P5J.MgAtAll
import Johnson.Road.K4.K4FillAll

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

open VerifiableInference.Desc.First (classA pubWide FoldData FoldFacts)
open Johnson.Desc.First.Walk.Tied (RchAt RchPub)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.OnPublicFiles (headLink)
open OnBytes.Slice (frS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The IOP as written in Lean, at the head's letters. -/
local notation "𝐅" => (P5J.F0T OnBytes.secondHashFunction Zp Np cF)

set_option quotPrecheck false in
/-- The first chain's frame, at the head's letters. -/
local notation "𝐅𝐫" => (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)

/-- **K4's SHARE IN THE FORM IN WHICH A KIND's LAW IS TO END, AT THE
CONSTANT.** NO MEMBER OF ITS BINDERS IS SHOWN ANYWHERE; under the
binders of `k04_of_head` (K04OfHead.lean) they are had; A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles`
AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). -/
theorem k04_kind (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (𝔏 : P5J.Free numsFull D 𝐅 P5J.At.Tok)
    (q₁ : (𝐅).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (𝐅).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (𝐅).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL 𝐅 Zp Bs base cF (Desc.K14.Law.seatZ Zp Np)
      (Desc.K14.Law.secondAt Zp Np))
    (L : VerifiableInference.Desc.K12.Door.Laid)
    (lw : ℕ → LW Cb.Gl.E)
    (Sn : ∀ g, g < 12 → ∀ x b, K4Here cF Zp Bs.G₀ g x b →
      K4NamedW hA.𝔇 (eAll Zp cF L) (28 * g + 4) (2 * g) (parOf x)
      (cF.blocksInOrder.map fun b => b.oracles.flatMap id)
        (Forest.elems (P5J.At.X Zp).y.fo))
    (hNf : ∀ g, g < 12 →
      Rec.nextFitsB (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).cs
      (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).d12.M
      ((k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).N.msgsAt
      (flatPlacesOf linksFull true)[28 * g + 4 + 1]?)
        (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).N.indexNo
        (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).free0
        (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).fvs (2 * g) = true)
    (Pf : K4PinsFill hA.𝔇 Zp)
    (Pt : ∀ g, g < 12 → ∀ x b, K4Here cF Zp Bs.G₀ g x b →
      K4PinsTests hA.𝔇 (eAll Zp cF L) Zp (28 * g + 4) g (parOf x))
    (W : WrittenAt Zp)
    (reqT : ReqTies (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).reqB
    (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).reqW
      (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).H.req (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).put)
    (Pp : ProofFile.InstPub → Prop)
    (W0 : ∀ g, g < 12 → ∀ a : (ProofFile.InstPub × S) × 𝐅𝐫.E.Str,
      RchPub 𝐅 Pp (28 * g + 4) a → a.1.2.failed = none → WideFacts hA.𝔇 (eAll Zp cF L) a.1)
    (R0 : ∀ g, g < 12 → ∀ a : (ProofFile.InstPub × S) × 𝐅𝐫.E.Str,
      RchPub 𝐅 Pp (28 * g + 4) a → a.1.2.failed = none →
        Johnson.Desc.First.Walk.Tied.roomIsB (eAll Zp cF L).dP.free0 (eAll Zp cF L).dP.fvs (2 * g)
        a.1.2 = true)
    (L7 : ∀ g, g < 12 → ∀ a : (ProofFile.InstPub × S) × 𝐅𝐫.E.Str,
      RchPub 𝐅 Pp (28 * g + 4) a → a.1.2.failed = none →
        (((eAll Zp cF L).dP.tl (2 * g)).any fun tlP =>
          VerifiableInference.Desc.First.K8.Ready.lay7B tlP a.1.2) = true) :
    KindTiedR (Fr := 𝐅𝐫) (P5J.At.N Zp cF) (P5J.mgAt hA.toAtMg hA.𝔇) P5J.fullLinks P5J.At.ps
      (RchPub 𝐅 Pp) (hA.toAtMg.ex 𝔏) (hA.toAtMg.row 𝔏) KindName.K4 := by
  obtain ⟨hT, hc, hcap⟩ := P5J.AtMg.pieces hA.toAtMg 𝔏 q₁ q₂ q₃
  have hp := planOk_parts 𝐅 hA.laid.planOk
  have hH : isLay hA.𝔇.links (headLink (P5J.At.X Zp)) = false := by
    rw [P5J.headLink_in_scope hA.scope hA.reads hA.pubOne]
    exact (by decide : isLay linksFull 24 = false)
  have hkC : hA.𝔇.P13.lin.kCol = kRef :=
    Nat.pow_right_injective (le_refl 2) (show 2 ^ hA.𝔇.P13.lin.kCol = 2 ^ kRef from hA.cols13)
  exact k04_law_front hA.scope hA.reads O hT "proof file"
    (by rw [P5J.LaidAt.atDepth hA.scope hA.laid]; exact hA.laid.data) hp.2.2.2 _ _ _ _ _ _ _ _ _ _
    hc hcap hp.1 O.W hA.𝔇 (eAll Zp cF L) rfl hkC hH (hA.toAtMg.ex 𝔏)
    (P5J.AtMg.ex_quiet hA.toAtMg 𝔏) lw (k4Fill_all hA L) Sn hNf Pf Pt W reqT Pp W0 R0 L7

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k04_kind
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
set_option pp.proofs true in
#check @OnBytes.Road.K4.k04_kind
