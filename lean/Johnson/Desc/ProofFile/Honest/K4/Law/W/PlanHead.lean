-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/PlanHead.lean: CONDITIONAL.

What is here. The hypothesis `K4Plan` (Johnson/Road/K4/W/GroundOfHear.lean: nine public facts on the
plan of the feed-forward layers' own rounds, sub-protocol K4) at the library's own public parameters
X, at the parameters of the member of the first chain: the shape of the layers and the calls are
X's, the sizes are the library's reference sizes `DF`, and THE PLAN OF THE SUB-PROOF IS `x.2.hp.tl`:
the plan at which Law/W/OneTie.lean's two fields stand. The library's `refPub_in_scope`
(Johnson/Road/K4/RefInScope.lean) has nineteen public facts there (`PubLines`,
Johnson/Road/K4/PubAt.lean); nine of them are `K4Plan`'s fields. Three statements; each proof is
that call.

  `k4Plan_head`   `K4Plan` at X's own data of the layers with any tokens, at a group below 12 and
      its plan hp: at hp.tl.
  `wsLay_head`   one more of the nineteen: the layout of the committed matrix of weights.
  `plan_head`   **`K4Plan (layerShape X.P) X.P.polCalls (parOf x).P (parOf x).g x.2.hp.tl DF`.**

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. The side library AtFullSide proves,
with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). Lh (`LaidK4`,
Law/SeatedHead.lean): on public lists and numbers; it follows from h at each of the twelve groups
(`laid_at`, Law/LaidAtGroup.lean), and hG is one of its fields: so hg, hG and Lh ask nothing beyond
h. THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on
soundness, on completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 19 modules under Johnson/Goal/ and at 5 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 24 is not counted: all the numbers are floors. They come with
h, with Law/SeatedHead.lean and with Johnson/Road/K4/RefInScope.lean, whose `refPub_in_scope` calls
a statement of a file under Johnson/Goal/ (`Meaning.P34.pub34_all`): ALL THREE STATEMENTS REST ON
IT. A LAW, NOT A PART: no file that defines a part of the proof file's description may import this
one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedHead
import Johnson.Road.K4.RefInScope
import Johnson.Road.K4.W.GroundOfHear

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (parOf refPub_in_scope)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Maker (WholeD)
open Inst.Model.All (DF)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **`K4Plan` AT THE PUBLIC PARAMETERS' OWN DATA OF THE LAYERS, with any tokens tk.** CONDITIONAL:
on h, hg and hG. -/
theorem k4Plan_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} {hp : Layer.HPlan2}
    (hg : g < 12) (hG : (P5J.At.X Zp).G[g]? = some hp) (tk : Array Nat) :
    K4Plan (Verify.layerShape (P5J.At.X Zp).P) (P5J.At.X Zp).P.polCalls
      { (P5J.At.X Zp).layers with tokv := tk } g hp.tl DF := by
  obtain ⟨_, HL, _, _⟩ := (refPub_in_scope h.scope h.reads h.pubOne hg).lines hp hG
  have PL := HL tk
  exact
    { lay := PL.hy
      sw := PL.S
      scales := PL.hs
      grp := PL.hg
      reads := PL.hrd
      tails := PL.hmats
      mats := PL.htm
      NM := PL.hNM
      sized := PL.Z }

/-- **The layout of the committed matrix of weights is made of the public parameters' own shape.**
CONDITIONAL: on h, hg and hG. -/
theorem wsLay_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} {hp : Layer.HPlan2}
    (hg : g < 12) (hG : (P5J.At.X Zp).G[g]? = some hp) :
    wsLayOf (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y) true Inst.Model.Layout.kRef =
      .ok (P5J.At.X Zp).layers.wsLay := by
  obtain ⟨_, HL, _, _⟩ := (refPub_in_scope h.scope h.reads h.pubOne hg).lines hp hG
  exact (HL #[]).hlw

/-- **`K4Plan` AT THE MEMBER's OWN PARAMETERS.** CONDITIONAL: on h and Lh. -/
theorem plan_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) :
    K4Plan (Verify.layerShape (P5J.At.X Zp).P) (P5J.At.X Zp).P.polCalls (parOf x).P (parOf x).g
      x.2.hp.tl DF := by
  have eP : x.2.P = { (P5J.At.X Zp).layers with tokv := (P5J.At.X Zp).layers.tokv } := Lh.P
  show K4Plan _ _ x.2.P x.2.g x.2.hp.tl DF
  rw [eP, Lh.grp]
  exact k4Plan_head h Lh.lt Lh.hp _

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4Plan_head
#print axioms ProofFile.Honest.K4.W.wsLay_head
#print axioms ProofFile.Honest.K4.W.plan_head
