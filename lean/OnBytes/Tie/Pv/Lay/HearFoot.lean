-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/HearFoot.lean: the last stages of a layers' sub-proof's own messages, behind the
batched sumcheck of the inner products: what the verifier's routines have heard where they succeed,
in the order of the chain of Cb/Pv/Lay/Own.lean.

Main names:
  `footStages`: the ten stages: the gated products' sumcheck and its LINE; an idle step; the point
    of the routed layers' join; the routed gated products' sumcheck and its LINE; an idle step; the
    round that batches the claims on the weights, with the embedding's scalar in the first group;
    the merge's sumcheck; an idle step.
  `foot_heard`: from the successes of hearGated, of the embedding's scalar and of wsForkEnd, one
    after the other (as `hearOwn_ran` gives them, OnBytes/Tie/Pv/Lay/HearOwn.lean), with routed
    experts and more than one layer bit: these stages were heard, with the two layers' records and
    the merge's.

Limits: those of OnBytes/Tie/Pv/Lay/HearL.lean and HearGated.lean.
-/
import OnBytes.Tie.Pv.Lay.HearGated
import OnBytes.Tie.Pv.Lay.HearOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Model.Layer
open OnBytes.Psc (Weight hearMany hearOne)
open OnBytes.Tie.Pv.Att (PscH)

/-- The last stages. -/
def footStages (P : Pub) (H : Heard) (K : HeardStack) (tT : Tsc) (hd hd2 : Level) (H5 H6 H7 : PscH)
    (d : Fmt.Drawn) (vE : List E) (rows : Nat) (x : E) : List StageL :=
  [.sum [] (levelWeights P.rd.muH (downFrom K.rs K.fin.wD ++ H.ztF) (orderRange P.rd.muH)) 2 H5,
    .line hd.tau, .idle, .point .join d,
    .sum [] (levelWeights P.rd.muH2
      ((d.elems.map E.ofTriple).toArray ++ downFrom K.rs P.y.lfe ++ tT.r)
      (orderRange P.rd.muH2)) 2 H6, .line hd2.tau, .idle] ++
  [.bat vE rows x, .sum [] (List.replicate P.wsLay.lk (Weight.plain 3)) 1 H7] ++ [.idle]

theorem foot_heard (P : Pub) (H : Heard) (K : HeardStack) (b : Bool) (claims : Array WsClaim)
    (sv : Nat → Array Nat) (hd : Level) (o2 : Option Level) (sVE : Nat) (wo : WsForkOut)
    (F3 F4 F5 G : Fork) (c3 c4 c5 c6 c' : Ctx) (hp : P.y.h.p3 = true) (hl : P.y.h.ll > 1)
    (h4 : hearGated P H K F3 c3 = .ok (((hd, o2), F4), c4))
    (h5 : embScalar b F4 c4 = .ok ((sVE, F5), c5))
    (h6 : wsForkEnd P.wsLay claims (sv sVE) F5 c5 = .ok ((wo, G), c6)) (s6 : Still c6 c')
    (hs : Sized F3) :
    ∃ (hd2 : Level) (tT : Tsc) (H5 H6 H7 : PscH) (d : Fmt.Drawn) (vE : List E) (x : E),
      o2 = some hd2 ∧ H.tT = some tT ∧
      HeardL (footStages P H K tT hd hd2 H5 H6 H7 d vE (sv sVE).size x) c3 c' ∧
      GatedSaid P H K F3 F4 hd hd2 H5 H6 d ∧ vE.length = (if b then 1 else 0) ∧
      (b = true → sVE = F4.next ∧ Filled (taken F4 1) F5 F4.next vE oneE) ∧ (b = false → F5 = F4) ∧
      MergeSaid P.wsLay claims (sv sVE) F5 G wo x H7 := by
  obtain ⟨hd2, tT, H5, H6, d, e1, e2, p4, q4⟩ := gated_heard P H K F3 F4 c3 c4 hd o2 hp hl h4 hs
  have hs4 : Sized F4 := by
    obtain ⟨_, _, _, _, a⟩ := q4.said
    exact a.sized
  obtain ⟨vE, a1, a2, a3, a4, a5⟩ := embScalar_open b F4 F5 c4 c5 sVE h5 hs4
  obtain ⟨x, H7, p6, q6⟩ := merge_heard P.wsLay claims (sv sVE) F5 G c5 c6 wo h6 a3 vE c4 a1
  exact ⟨hd2, tT, H5, H6, H7, d, vE, x, e1, e2,
    HeardL.append _ _ c3 c6 c' (HeardL.append _ _ c3 c4 c6 p4 p6) s6.heard, q4, a2, a4, a5, q6⟩

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.foot_heard
