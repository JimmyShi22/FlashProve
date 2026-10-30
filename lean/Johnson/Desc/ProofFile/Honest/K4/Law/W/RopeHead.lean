-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/RopeHead.lean: CONDITIONAL.

What is here. Two fields of Law/W/FootB1.lean's `FootB1` (what is left as a hypothesis at one state
behind the step of the member of the feed-forward layers' own rounds, sub-protocol K4) HOLD UNDER
THE LIBRARY's HYPOTHESIS ON THE PUBLIC FILES (h: `P5J.AtMgA`), at each of the twelve groups of
layers, at the library's reference sizes and tables: the field rope (the rotary tables fit at every
end point) and the field qk (what the library's law on the panel of queries and keys asks of the
sizes and of the shifts). The first is the second field of the library's `RefPub`
(Johnson/Road/K4/RefPub.lean), which `refPub_in_scope` (Johnson/Road/K4/RefInScope.lean) has under
h. The second is Law/QkOfPlan.lean's `qk_of_plan` at Law/W/PlanHead.lean's `k4Plan_head` and the
library's `ref_chOK`.

  `rope_head`   **the field rope, with the field's own variable names**, at every public data Q
     whose layers' data are the public structure's and whose group is g, and every environment v
     with Q's layout, scales and group.
  `qk_head`   **the field qk, with the field's own variable names**, at every such environment.
  `rope_member`, `qk_member`   the two at the member's own public data (`k4PubAt`,
     Law/DearTop.lean), under `LaidK4`.

Limits. NOTHING NEW IS SHOWN: calls and rewritings. h and `LaidK4` are hypotheses; h and g < 12 give
`LaidK4` at the group g (`laid_at`, Law/LaidAtGroup.lean, which is not imported here). On h: the
side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with hg and the equations on Q and on v (hP hQg hG; vy vs vg), or with Lh
(`LaidK4`) and the three on v, no example is known to us. h STANDS AT THE LIBRARY's FULL-SIZE
STRUCTURE AND AT THE FORMAT's EARLIER HASH: THE STATEMENTS HOLD THERE ALONE. The three equations on
v (vy vs vg) are hypotheses: at what a hearing returned the library's `env_of_hear`
(Johnson/Road/K4/NormWordsOfHear.lean) has them. PUBLIC FACTS ALONE: what `FootB1` asks beside these
two is not touched, above all the lookup's own sentence. A LAW, NOT A PART: the statements rest,
through `refPub_in_scope`, on `Meaning.P34.pub34_all`, a statement of a file under Johnson/Goal/: no
file that defines a part of the proof file's description may import this one. WHAT THIS FILE's
IMPORTS REACH, by a program's walk over import lines that stops, unopened, at every module under
Johnson/Goal/, Johnson/D/, Johnson/Bridge/, Cb/Bridge* or ThirdParty/: it stopped at 71 modules
under Johnson/Goal/, at seven under Johnson/Bridge/ and at one under Cb/Bridge*, at none under the
two others; it saw 46 modules whose names hold RecCompile, none of them RecCompile.Honest…,
RecCompile.Both… or RecCompile.PassH…. What lies behind the 79 is not counted: the numbers are
floors. They come with h, with Law/W/PlanHead.lean and with Law/DearTop.lean.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.QkOfPlan
import Johnson.Desc.ProofFile.Honest.K4.Law.W.PlanHead
import Johnson.Desc.ProofFile.Honest.K4.Law.DearTop
import Johnson.Road.K4.RefInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road (sclOf RopeFits)
open OnBytes.Road.K4 (refPub_in_scope)
open OnBytes.Maker (WholeD)
open Inst.Model (tbRef)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (ref_chOK)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **THE ROTARY TABLES FIT AT EVERY END POINT, UNDER h.** CONDITIONAL: on h, hg, hP, hQg and the
three equations on v. THE FULL SIZE ALONE (h). -/
theorem rope_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12) {Q : K4Pub}
    (hP : Q.P = (P5J.At.X Zp).layers) (hQg : Q.g = g) {v : OnBytes.Model.Layer.Env}
    (vy : v.y = Q.P.y) (vs : v.sc = Q.P.sc) (vg : v.g = Q.g) (rs : Array E) :
    ∀ (rt : Array E) (lam : ℕ), lam < Q.P.y.Lam →
      RopeFits Reading.gl { v := v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := rs, rt := rt } DF
        tbRef (Q.g * Q.P.y.Lam) lam := by
  intro rt lam hl
  rw [hP] at vy vs hl ⊢
  rw [hQg] at vg ⊢
  exact (refPub_in_scope h.scope h.reads h.pubOne hg).rope v vy vs vg rs rt lam hl

/-- **WHAT THE LAW ON THE PANEL OF QUERIES AND KEYS ASKS, UNDER h.** CONDITIONAL: on h, hg, hG, hP,
hQg and the three equations on v. THE FULL SIZE ALONE (h). -/
theorem qk_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12) {hp : HPlan2}
    (hG : (P5J.At.X Zp).G[g]? = some hp) {Q : K4Pub} (hP : Q.P = (P5J.At.X Zp).layers)
    (hQg : Q.g = g) {v : OnBytes.Model.Layer.Env} (vy : v.y = Q.P.y) (vs : v.sc = Q.P.sc)
    (vg : v.g = Q.g) :
    letI : Inst.Model.Scl := sclOf (Verify.layerShape (P5J.At.X Zp).P) v.sc v.g v.y.Lam
    DF.ChOK ∧ ∀ l, l < DF.nl →
      (DF.Pl l).kq = (DF.Pl l).kk ∨ (16 ≤ (DF.Pl l).kq ∧ 16 ≤ (DF.Pl l).kk) := by
  rw [vy, vs, vg, hP, hQg]
  exact qk_of_plan (k4Plan_head h hg hG (P5J.At.X Zp).layers.tokv) ref_chOK

/-- **The rotary tables at the member's own public data.** CONDITIONAL: on h, Lh and the three
equations on v. THE FULL SIZE ALONE (h). -/
theorem rope_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {v : OnBytes.Model.Layer.Env}
    (vy : v.y = (k4PubAt cF k x).P.y) (vs : v.sc = (k4PubAt cF k x).P.sc)
    (vg : v.g = (k4PubAt cF k x).g) (rs : Array E) :
    ∀ (rt : Array E) (lam : ℕ), lam < (k4PubAt cF k x).P.y.Lam →
      RopeFits Reading.gl
        { v := v, wsLay := (k4PubAt cF k x).P.wsLay, rope := (k4PubAt cF k x).P.rope, rs := rs,
          rt := rt } DF tbRef ((k4PubAt cF k x).g * (k4PubAt cF k x).P.y.Lam) lam :=
  rope_head h Lh.lt Lh.P Lh.grp vy vs vg rs

/-- **The panel of queries and keys at the member's own public data.** CONDITIONAL: on h, Lh and the
three equations on v. THE FULL SIZE ALONE (h). -/
theorem qk_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {v : OnBytes.Model.Layer.Env}
    (vy : v.y = (k4PubAt cF k x).P.y) (vs : v.sc = (k4PubAt cF k x).P.sc)
    (vg : v.g = (k4PubAt cF k x).g) :
    letI : Inst.Model.Scl := sclOf (Verify.layerShape (P5J.At.X Zp).P) v.sc v.g v.y.Lam
    DF.ChOK ∧ ∀ l, l < DF.nl →
      (DF.Pl l).kq = (DF.Pl l).kk ∨ (16 ≤ (DF.Pl l).kq ∧ 16 ≤ (DF.Pl l).kk) :=
  qk_head h Lh.lt Lh.hp Lh.P Lh.grp vy vs vg

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.rope_head
#print axioms ProofFile.Honest.K4.W.qk_head
#print axioms ProofFile.Honest.K4.W.rope_member
#print axioms ProofFile.Honest.K4.W.qk_member
