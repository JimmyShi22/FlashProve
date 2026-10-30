-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MatsAreHead.lean: CONDITIONAL.

What is here. THE NAMED READING OF THE CELLS `MatsAre` (Johnson/Desc/First/Look/K3CallerLay.lean)
HOLDS AT EVERY WITNESS, under the library's hypothesis h, `LaidK4` and hx, which names the place: at
the lookup's place of the segment of the feed-forward layers' own rounds (sub-protocol K4), in every
group: the matrices that the lookup's caller reads off a witness are the casts of the list of
integers that the library's meaning reads off the same witness for the group (`(h.𝔇.H.hid w).MG g`).
At the script's witness, at every continuation of the challenges heard, it is the hypothesis hA of
`emb_head` (Law/W/EmbHead.lean), of `k4_idn_tie` (Law/W/OneTie.lean) and of `k4_exchange_tenth`
(Law/ExchangeTenth.lean), and an instance of the hA of `cellsTie_of_tie` (Law/W/OneTie.lean). No
thread, script, state or prover is named in it. No file calls it. How:
Johnson/Road/K4/W/MatsOwn.lean has the equation from four conditions on public letters; three are
fields of the library's `fitF_wide` (Johnson/Road/K4/K4PinsFirstWhole.lean), had as in `sitsIn_head`
(Law/W/ReadersHead.lean): its one test `firstFastB` is a field of `pinsTests_head` (the same file;
the library's `first_paid`); the fourth, at the seam in front of a later group, is a field of the
library's `fit_wide` (K4PinsFitAtWide.lean), which asks that test and two more, `commonFastB` and
`seamFastB`: these the library's `common_paid` and `seam_paid` (K4PlanPaid.lean) have from the
written values; and the meaning's list is the one that MatsOwn.lean speaks of by the library's
`pinsFill_const` (K4PinsFirstScope.lean). The proof is a chain of calls.

  `matsAre_head`   **`MatsAre` at the list of the group, at every witness.**

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. Lh (`LaidK4`, Law/SeatedHead.lean)
and hx: on public lists and numbers; both follow from h at each of the twelve groups (`laid_head`,
the same file, with the library's `atK4_full`; `layAt_laid`, Law/W/LayAtHead.lean): so Lh and hx ask
nothing beyond h. WHAT IT SAYS: that two of the library's readers of one witness read one thing, at
all indices, 0 outside every size on both sides. NOTHING ON WHAT A CELL IS WORTH, on an honest
prover's cells (`CellIsList` stays a hypothesis of the tops), on weights, tokens, coins or the mask
row. Beneath the library's tests stand closed facts on written values that Lean's kernel has decided
in the library; whether an independent checker has replayed these is not said here. Beneath
`nine_head` (Law/ElevenHead.lean), which is called, stands one more such comparison (`decide
+kernel`); no independent checker has replayed it. The side library AtFullSide proves, with no
hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). No test stands beside
it. THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on
soundness, on completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. THE
STATEMENT RESTS ON STATEMENTS OF FILES UNDER Johnson/Goal/, CALLED BY NAME: `Meaning.scope_plans`
(Johnson/Goal/Meaning/PlanShapes.lean) and `OnBytes.Road.Hd.core_of_scope`
(Johnson/Goal/Meaning/ScopeCore.lean), as Law/W/ReadersHead.lean's do; the proof writes the
library's `Meaning.mgOf`, `Meaning.sizesOf`, `Meaning.seatBy` and `Meaning.fLay` by name; and
`common_paid` and `seam_paid` call `Meaning.nmFit_of_core`, `Meaning.planFit_of_core` and
`Meaning.pairs_of_planFit` (Johnson/Road/K4/K4PlanPaid.lean imports two files under Johnson/Goal/
for them). A LAW, NOT A PART: no file that defines a part of the proof file's description may import
this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ReadersHead
import Johnson.Road.K4.W.MatsOwn
import Johnson.Road.K4.K4PinsFitAtWide
import Johnson.Road.K4.K4PlanPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (eAll parOf written_of_head fitF_wide fit_wide common_paid seam_paid
  pinsFill_const group_at layAt_plan cutW posFree refPub_in_scope ownW)
open OnBytes.Road.K4.W (mats_mg)
open OnBytes.Maker (WholeD)
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.PlanWritten (publicSteps_of)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First.Look (layAt MatsAre Stored.entries)
open VerifiableInference.Desc.Sound (mgBase)
open VerifiableInference.OnPublicFiles (layMs)
open P5J (AtMgA TS)
open ProofFile.Honest.FirstThread (WtF)
open ProofFile.Honest.K4.SeatedHead (LaidK4 k4Here_head)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h, Lh and hx. **`MatsAre` AT THE LIST OF THE GROUP, AT EVERY WITNESS.** xl: the
lookup's place at the segment. w: any witness. -/
theorem matsAre_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    (w : WtF) :
    MatsAre xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
      (layMs xl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr
        h.𝔇.l3.msgW w)
      ((h.𝔇.H.hid w).MG g) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, hG, -, Hh⟩ := k4Here_head h Lh
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := O.W ▸ O.public
  have N := nine_head h Lh
  obtain ⟨x₁, hx₁, el, e1, e2, e3, _⟩ := layAt_plan N.Sx.pubOf N.Sx.notHead N.Sx.step N.Sx.plan
  have ex : x₁ = xl := Option.some.inj (hx₁.symm.trans hx)
  rw [ex] at el e1 e2 e3
  obtain ⟨k4, _, _⟩ := _root_.Meaning.scope_plans h.scope h.reads hpub
  have Pf := pinsFill_const OnBytes.secondHashFunction Zp Np cF (P5J.At.EAt Z) h.plan.shape Z.lay h.plan.laid
    h.plan.hN h.plan.hG xh OnBytes.Flat.numsFull.rows
  obtain ⟨radM, Q3⟩ := Pf.ms
  have eg : (parOf x).g = g := Lh.grp
  have Pt := pinsTests_head h Lh
  have W := written_of_head h.toAtMg
  have C := OnBytes.Road.Hd.core_of_scope h.scope h.reads hpub
  have F := fitF_wide Zp radM h.𝔇 (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase
    (parOf x)
    Pf.sent Pf.arr Q3 Pf.nSent Pf.nIndex Pf.seat3 (by rw [eg]; exact Pt.first)
    (by rw [eg]; exact Lh.lt) xl (by rw [el, eg]; exact Lh.seg) (O.W ▸ Hh.G) (posFree 0)
    (publicSteps_of hpub) (refPub_in_scope h.scope h.reads hpub (by rw [eg]; exact Lh.lt))
    (O.W ▸ Hh.P) ⟨e1.trans N.Sx.shape, by rw [N.Sx.y]; exact e2, e3⟩ (group_at k4 _)
    (by rw [eg, ← Lh.seg]; exact N.Sx.notHead)
  have hs := sitsIn_head h Lh hx
  have hσ := F.size
  have h1 := F.syms
  have hS := fun (gp : 0 < (parOf x).g) =>
    (fit_wide Zp radM h.𝔇 (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase (parOf x)
      Pf.sent Pf.arr Q3 Pf.nSent Pf.nIndex Pf.seat3 (common_paid W hpub C)
      (by rw [eg]; exact Pt.first) (seam_paid W hpub C gp (by rw [eg]; exact Lh.lt)) gp
      (by rw [eg]; exact Lh.lt) xl (by rw [el, eg]; exact Lh.seg) (O.W ▸ Hh.G) (posFree 0)
      (publicSteps_of hpub) (refPub_in_scope h.scope h.reads hpub (by rw [eg]; exact Lh.lt))
      (O.W ▸ Hh.P) ⟨e1.trans N.Sx.shape, by rw [N.Sx.y]; exact e2, e3⟩ (group_at k4 _)
      (by rw [eg, ← Lh.seg]; exact N.Sx.notHead)).seam
  rw [eg] at hσ h1 hS
  have eH : (h.𝔇.H.hid w).MG g =
      _root_.Meaning.mgOf Zp.p.X.y
        (ownW h.𝔇.arr h.𝔇.ms h.𝔇.N (_root_.Meaning.sizesOf Zp.p.X)
          (_root_.Meaning.seatBy (_root_.Meaning.fLay (OnBytes.Road.K4.sentAt Zp).layout
            (OnBytes.Road.K4.numAt Zp)) Zp.p.X
            (_root_.Meaning.sizesOf Zp.p.X)) h.𝔇.cs w) g := Pf.hid g w
  unfold MatsAre
  rw [eH]
  exact mats_mg xl h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xl.link false j.1)
    (cutW Stored.entries h.𝔇.l3.wOf hRef (2 ^ kRef)) (posFree 0) x.2.hp.tl h.𝔇.l3.oW h.𝔇.l3.wOf
    h.𝔇.l3.nr h.𝔇.l3.nc h.𝔇.l3.arr h.𝔇.ms h.𝔇.N (2 * g) h.𝔇.l3.msgW
    (_root_.Meaning.sizesOf Zp.p.X)
    (_root_.Meaning.seatBy (_root_.Meaning.fLay (OnBytes.Road.K4.sentAt Zp).layout
            (OnBytes.Road.K4.numAt Zp)) Zp.p.X
      (_root_.Meaning.sizesOf Zp.p.X)) Zp.p.X.y g hs hσ h1 hS w

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.matsAre_head
