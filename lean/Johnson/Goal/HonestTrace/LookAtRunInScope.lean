-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/LookAtRunInScope.lean

The four statements on ThreeFacts and ClaimsZero of Johnson/HonestTrace/LookAtRun.lean, and
claimsZero_head_foRun of Johnson/HonestTrace/LookAtRunFo.lean, for public files in scope, at the
trace theTrace X i x of a served request.
This file states no goal.

"The three premises on the public files" are: VerifierAndGoals.InScope Z = true; VerifierAndGoals.readFiles Z returns;
publicOf returns X on Z's parameter and scale files, at any third argument.

Main theorems, under these three:
* "headT_in_scope": X.hS.T = 1,024.
* "facts_layers_run_in_scope", "claimsZero_layers_run_in_scope": if ServesAt X i x, for g < 12 and
  every t: ThreeFacts and ClaimsZero with the key vectors G.kvG { X.layers with tokv := t } g read
  from theTrace X i x, under the premises on ν (and on θ and C) of facts_layers and
  claimsZero_layers.
* "facts_head_run_in_scope", "claimsZero_head_run_in_scope": if ServesAt X i x, for R with R.h =
  X.hS, R.L = X.HLy and Hd.ReqFits R HeadSizes.ref (Head.Req.of pl x), for any policy pl: the same
  with the key vectors H.kvH (Hd.pubH R (borderOf X.y) X.layers.wsLay).
* "claimsZero_head_foRun_in_scope": if besides R.b = borderOf X.y: ClaimsZero with the key vectors
  H.kvH (Fo.pubH R X.layers.wsLay).

Limits. R.h = X.hS, R.L = X.HLy, R.b = borderOf X.y and Hd.ReqFits are premises: none is shown here
of a run. The limits of the two files named and of Johnson/Goal/HonestTrace/LookInScope.lean hold
here. The bundle AllFacts is not restated; of Johnson/HonestTrace/LookAtRunFo.lean neither
facts_head_foRun nor the two forms at Fo.Pub2.pubHAt are.

That the premises can be met together is known thinly. "premises_met_of_public"
(Johnson/Goal/HonestTrace/FullInScope.lean) meets the three premises on the public files and
ServesAt at the stored full-size example's files, at some index and a request with r = 1,023 and e =
1,024, which has no counted position (in its proof all weights and tokens are 0); and that publicOf
returns at these files is a premise of that theorem, which this library checks by an evaluation (a
#guard in Johnson/Goal/Meaning/ScopeRun.lean, whose head says that it is no theorem). Of R: the
value Hd.runReq (runAt X) x meets R.h = X.hS, R.L = X.HLy, R.b = borderOf X.y and Hd.ReqFits, and it
is no run. No theorem cited here exhibits public files, an index, a request and a value R of a run
that meet all premises together.

Not claimed: that a verifier accepts these rounds; that a prover's program sends them; completeness
of the protocol.

-/
import Johnson.HonestTrace.LookAtRunFo
import Johnson.Goal.HonestTrace.LookInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Model OnBytes.Ends
open OnBytes.Model.Verify (borderOf publicOf)
open OnBytes.Road
open OnBytes.Road.Alg (cellMW)
open OnBytes.Road.Hd (readH)
open Look

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  {i : Cm.Idx} {x : Instance ppref}

/-- Under the three premises on the public files: the head has 1,024 positions. -/
theorem headT_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : X.hS.T = 1024 := by
  have B := (Hd.eleven_of_core h (Hd.core_of_scope hZ hR h) (Hd.npOf X.hS)).1
  show 2 ^ X.hS.lt = 1024
  rw [B.full.lt]

/-- In scope, at a served request, for g < 12 and every t: under the premise on ν of facts_layers,
ThreeFacts with the key vectors G.kvG { X.layers with tokv := t } g, read from theTrace X i x. -/
theorem facts_layers_run_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    (S : ServesAt X i x) (t : Array ℕ) {g : ℕ} (hg : g < 12) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.y.h.lmb, ∀ c < X.y.fo.NC * 2 ^ (X.y.fo.kT + 5 - X.y.h.lmb),
      ν (.cell r c) = cellMW (theTrace X i x (2 * g)) i.mat (.cell (G.iB X.y) r c)) :
    ThreeFacts X.y.fo
      (G.kvG { X.layers with tokv := t } g (cellMW (theTrace X i x (2 * g)) i.mat))
      (fun u j => G.bitsG X.y (cellMW (theTrace X i x (2 * g)) i.mat) (u * 32 + j))
      X.y.h.lmb ν :=
  facts_layers_run (lookPub_in_scope hZ hR h) (meetsAll_theTrace hZ hR h S)
    (planesLaid_in_scope hZ hR h i x) t hg ν hν

/-- In scope, at a served request, for g < 12 and every t: under the premises on ν, θ and C of
claimsZero_layers, ClaimsZero with the key vectors G.kvG { X.layers with tokv := t } g, read from
theTrace X i x. -/
theorem claimsZero_layers_run_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    (S : ServesAt X i x) (t : Array ℕ) {g : ℕ} (hg : g < 12) (jLK : ℕ)
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.y.h.lmb, ∀ c < X.y.fo.NC * 2 ^ (X.y.fo.kT + 5 - X.y.h.lmb),
      ν (.cell r c) = cellMW (theTrace X i x (2 * g)) i.mat (.cell (G.iB X.y) r c))
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several X.y.fo = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits X.y.fo.v X.y.fo.d 5) :
    ClaimsZero X.y.fo X.y.h.lmb jLK
      (G.kvG { X.layers with tokv := t } g (cellMW (theTrace X i x (2 * g)) i.mat)) θ al ν C :=
  claimsZero_layers_run (lookPub_in_scope hZ hR h) (meetsAll_theTrace hZ hR h S)
    (planesLaid_in_scope hZ hR h i x) t hg jLK ν hν h0 θ al h1 C hC

/-- In scope, at a served request, for R with R.h = X.hS, R.L = X.HLy and Hd.ReqFits of R at
HeadSizes.ref and Head.Req.of pl x: under the premise on ν of facts_head, ThreeFacts with the key
vectors H.kvH (Hd.pubH R (borderOf X.y) X.layers.wsLay), read from theTrace X i x. -/
theorem facts_head_run_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    (S : ServesAt X i x) (pl : AcceptancePolicy) (R : Head.Run) (hh : R.h = X.hS) (hL : R.L = X.HLy)
    (Rq : Hd.ReqFits R HeadSizes.ref (Head.Req.of pl x)) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (theTrace X i x 24) i.mat (.cell (X.hS.NHf + 2) r c)) :
    ThreeFacts X.HLy.fs
      (H.kvH (Hd.pubH R (borderOf X.y) X.layers.wsLay) (readH (theTrace X i x 24) i.mat))
      (fun u j => H.bitsH X.hS X.HLy.fs (readH (theTrace X i x 24) i.mat) (u * 32 + j))
      X.hS.lmbH ν :=
  facts_head_run (lookPub_in_scope hZ hR h) (meetsAll_theTrace hZ hR h S)
    (planesLaid_in_scope hZ hR h i x) (headT_in_scope hZ hR h) pl R hh hL Rq ν hν

/-- In scope, at a served request, for R as in facts_head_run_in_scope: under the premises on ν, θ
and C of claimsZero_head, ClaimsZero with the key vectors H.kvH (Hd.pubH R (borderOf X.y)
X.layers.wsLay), read from theTrace X i x. -/
theorem claimsZero_head_run_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    (S : ServesAt X i x) (pl : AcceptancePolicy) (R : Head.Run) (hh : R.h = X.hS) (hL : R.L = X.HLy)
    (Rq : Hd.ReqFits R HeadSizes.ref (Head.Req.of pl x)) (jLK : ℕ) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (theTrace X i x 24) i.mat (.cell (X.hS.NHf + 2) r c))
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several X.HLy.fs = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits X.HLy.fs.v X.HLy.fs.d 5) :
    ClaimsZero X.HLy.fs X.hS.lmbH jLK
      (H.kvH (Hd.pubH R (borderOf X.y) X.layers.wsLay) (readH (theTrace X i x 24) i.mat))
      θ al ν C :=
  claimsZero_head_run (lookPub_in_scope hZ hR h) (meetsAll_theTrace hZ hR h S)
    (planesLaid_in_scope hZ hR h i x) (headT_in_scope hZ hR h) pl R hh hL Rq jLK ν hν h0 θ al h1
    C hC

/-- In scope, at a served request, for R as in facts_head_run_in_scope with R.b = borderOf X.y
besides: under the premises on ν, θ and C of claimsZero_head, ClaimsZero with the key vectors H.kvH
(Fo.pubH R X.layers.wsLay), read from theTrace X i x. -/
theorem claimsZero_head_foRun_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    (S : ServesAt X i x) (pl : AcceptancePolicy) (R : Head.Run) (hh : R.h = X.hS) (hL : R.L = X.HLy)
    (hb : R.b = borderOf X.y) (Rq : Hd.ReqFits R HeadSizes.ref (Head.Req.of pl x)) (jLK : ℕ)
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (theTrace X i x 24) i.mat (.cell (X.hS.NHf + 2) r c))
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several X.HLy.fs = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits X.HLy.fs.v X.HLy.fs.d 5) :
    ClaimsZero X.HLy.fs X.hS.lmbH jLK
      (H.kvH (_root_.Fo.pubH R X.layers.wsLay) (readH (theTrace X i x 24) i.mat)) θ al ν C :=
  claimsZero_head_foRun (lookPub_in_scope hZ hR h) (meetsAll_theTrace hZ hR h S)
    (planesLaid_in_scope hZ hR h i x) (headT_in_scope hZ hR h) pl R hh hL hb Rq jLK ν hν h0 θ al
    h1 C hC

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.headT_in_scope
#print axioms OnBytes.HonestTrace.facts_layers_run_in_scope
#print axioms OnBytes.HonestTrace.claimsZero_layers_run_in_scope
#print axioms OnBytes.HonestTrace.facts_head_run_in_scope
#print axioms OnBytes.HonestTrace.claimsZero_head_run_in_scope
#print axioms OnBytes.HonestTrace.claimsZero_head_foRun_in_scope
