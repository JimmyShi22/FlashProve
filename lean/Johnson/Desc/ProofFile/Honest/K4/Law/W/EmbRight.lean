-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/EmbRight.lean: CONDITIONAL.

Not shown here. THAT THE STREAM WHICH COMES IN IS THE EMBEDDING OF THE TOKENS: EmbCube (the
library's identity j11 at every feature and position) is a hypothesis ON THE WITNESS in emb_right.
emb_right STANDS AT THE LIBRARY's OWN SIZES ALONE (SizedW s ppref, kRef, Q.P.V = ppref.V): at
another plan the field emb of Opened has no road. That the claim is there, has its unit and passes
the verifier's test on a claim's shape: hypotheses. That the sampled values in p are what the
verifier has heard. That the hypotheses can hold together: no example is known. The import closure
holds what Law/SumMergeStart.lean's holds: files over the frame, and laws on masked sumchecks' sums
(Johnson/Desc/ProofFile/Honest/SumLaw/); by a walk of import lines none with RecCompile in its name,
none under Johnson/Goal/ or Johnson/D/. Nothing on soundness, on completeness or on any other
property. No property is claimed.

The embedding's hidden value as the honest side of the layers' own rounds (sub-protocol K4) computes
it (`embValue`, Johnson/Desc/K4/Honest/Merge.lean), read into the field: first as the library's
value of the embedding's claim on the committed matrix, which is the right side of the field embV of
`OpenedOwn` (Johnson/Road/K4/W/OpenedOwn.lean); then, under EmbCube, as the sum over the stream that
comes in, typed after the right side of the field emb of `Opened` (Johnson/Road/K4/W/Ground.lean).
That the letters meet these fields is said by no statement of this file.

  `emb_claim_read`   the value is the library's claimVal of the claim, at the matrix of the input's
      words read (wmOf). By `claimVal_read` (Law/SumMergeStart.lean).
  `emb_right`   the value is the stream's sum. By emb_claim_read and `emb_opened`
      (Johnson/Road/K4/W/EmbOpened.lean).
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumMergeStart
import Johnson.Road.K4.W.EmbOpened
import Johnson.Road.FormsKeysWLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open Finset
open OnBytes (E zeroE)
open OnBytes.Model (Reading WsClaim WsUnit WsShape wsLayOf wsClaimShape eqTab)
open OnBytes.Model.Layer (ClaimEnv)
open OnBytes.Road (pt UnitOK SizedW unitOK_of_layout)
open OnBytes.Road.K4.W (EmbCube emb_opened)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Pts claimEnvOf embClaim embValue)
open Inst.Model (Scl ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim Cell xS embR)
open Meaning.Emb (EmbNums)
open Blocks (ext)

variable {Q : K4Pub} {w : K4In} {p : Pts} {ce : ClaimEnv} {cl : WsClaim}

/-- What the honest side's claim environment holds of the public numbers. -/
theorem claimEnv_lay (hce : claimEnvOf Q p = some ce) : ce.wsLay = Q.P.wsLay := by
  unfold claimEnvOf at hce
  obtain ⟨v, _, e⟩ := Option.map_eq_some_iff.mp hce
  rw [← e]

/-- **The embedding's value reads as the library's value of its claim on the committed matrix.**
CONDITIONAL: on every hypothesis named. -/
theorem emb_claim_read (hg : (Q.g == 0) = true) (hce : claimEnvOf Q p = some ce)
    (hcl : ce.claimE p.ZE p.tkh Q.P.V w.tokv = some cl) {u : WsUnit}
    (hu : Q.P.wsLay.U[cl.ui]? = some u) (hs : wsClaimShape Q.P.wsLay cl = .ok ())
    (U : UnitOK Q.P.wsLay.lk u) :
    Reading.gl.val (embValue Q w p) =
      OnBytes.Road.claimVal Reading.gl Q.P.wsLay (wmOf w.w) cl := by
  have e : embClaim Q w p = some cl := by
    unfold embClaim
    rw [if_pos hg, hce]
    exact hcl
  unfold embValue
  rw [e]
  exact claimVal_read w.w hu hs U

/-- **THE EMBEDDING's VALUE READS AS THE SUM OVER THE STREAM THAT COMES IN**, where that stream is
the embedding of the tokens, at the library's own sizes. CONDITIONAL: on every hypothesis named. -/
theorem emb_right [scl : Scl] (hg : (Q.g == 0) = true) (hce : claimEnvOf Q p = some ce)
    (hcl : ce.claimE p.ZE p.tkh Q.P.V w.tokv = some cl) {u : WsUnit}
    (hu : Q.P.wsLay.U[cl.ui]? = some u) (hs : wsClaimShape Q.P.wsLay cl = .ok ())
    (s : WsShape) (Z : SizedW s ppref) (hl : wsLayOf s true kRef = .ok Q.P.wsLay)
    (hV : Q.P.V = ppref.V) (N : EmbNums ce.v.y) (hZ : p.ZE.size = ce.v.y.ls + ce.v.y.h.lt)
    (hk : p.tkh.size = ce.v.y.lPd - ce.v.y.ls) {D : Dim} {t : Cell → Cb.Gl.E}
    (hlT : D.lT = ce.v.y.h.lt)
    (hJ : EmbCube D t (embR ppref kRef (wmOf w.w)) (fun i => w.tokv.getD i 0) ce.v.y.h.d) :
    Reading.gl.val (embValue Q w p) =
      ∑ kh ∈ range (ce.v.y.h.d / ce.v.y.S2), Reading.gl.val ((eqTab p.tkh).getD kh zeroE) *
        ∑ r ∈ range (2 ^ ce.v.y.ls), Blocks.eqN ce.v.y.ls 0 (pt Reading.gl p.ZE) r *
          ext D.lT (fun i => xS D t 0 (kh * 2 ^ ce.v.y.ls + r) i)
            (fun j => pt Reading.gl p.ZE (ce.v.y.ls + j)) := by
  have eL := claimEnv_lay hce
  obtain ⟨hlk, hU⟩ := unitOK_of_layout hl
  have U : UnitOK Q.P.wsLay.lk u := by
    rw [hlk]
    exact (hU u (Array.mem_of_getElem? hu)).1
  rw [emb_claim_read hg hce hcl hu hs U, ← eL]
  rw [hV] at hcl
  exact emb_opened Reading.gl ce s Z (by rw [eL]; exact hl) N hZ hk hcl (wmOf w.w) hlT hJ

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.claimEnv_lay
#print axioms ProofFile.Honest.K4.W.emb_claim_read
#print axioms ProofFile.Honest.K4.W.emb_right
