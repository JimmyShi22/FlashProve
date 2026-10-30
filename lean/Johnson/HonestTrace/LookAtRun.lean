-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookAtRun.lean

ThreeFacts (Johnson/HonestTrace/FullFacts.lean) and ClaimsZero
(Johnson/HonestTrace/LookAtClaims.lean) at the public data of a run: at { X.layers with tokv := t }
for every t, and at the head at Hd.pubH of every value R of Head.Run that fits the request.

Why. facts_layers, facts_head, claimsZero_layers and claimsZero_head stand at X.layers and at
pubHAt X x. A run of the Lean verifier under OnBytes/Model/ works with other public data; by
Johnson/HonestTrace/FullPlanesRun.lean the key vectors read nothing in which these differ.

Main theorems, under LookPub X, MeetsAll X i x T and PlanesLaid X i x T:
* "facts_layers_run", "claimsZero_layers_run": for g < 12 and every t, ThreeFacts and ClaimsZero
  with the key vectors G.kvG { X.layers with tokv := t } g, under the premises on ν (and on θ and C)
  of facts_layers and claimsZero_layers.
* "kvH_run": if X.hS.T = 1,024, for R with R.h = X.hS, R.L = X.HLy and Hd.ReqFits of R at
  HeadSizes.ref and Head.Req.of pl x, for any policy pl: H.kvH at
  Hd.pubH R (borderOf X.y) X.layers.wsLay is H.kvH at pubHAt X x.
* "facts_head_run", "claimsZero_head_run": under the same: ThreeFacts and ClaimsZero with the key
  vectors
  H.kvH (Hd.pubH R (borderOf X.y) X.layers.wsLay), under the premises of facts_head and
  claimsZero_head.

Limits. One rewriting each over kvG_tokv, pubH_run, kvH_agree and agreeCov_of_reqFits; the limits of
the files named hold here. Attention's key vectors take no such public data, so of the bundle
AllFacts the layers' and the head's members alone are restated; the bundle is not. That a run has
R.h = X.hS, R.L = X.HLy and Hd.ReqFits is not shown in this file, nor X.hS.T = 1,024.

Not claimed: that a verifier accepts the rounds; anything on a prover's program.

-/
import Johnson.HonestTrace.FullPlanesRun
import Johnson.HonestTrace.FullFacts
import Johnson.HonestTrace.LookAtClaims

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Model OnBytes.Ends
open OnBytes.Model.Verify (borderOf)
open OnBytes.Road
open OnBytes.Road.Alg (cellMW)
open OnBytes.Road.Hd (readH)
open Look

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- Under the premises of facts_layers, for every t: ThreeFacts with the key vectors
G.kvG { X.layers with tokv := t } g. -/
theorem facts_layers_run (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T)
    (t : Array ℕ) {g : ℕ} (hg : g < 12) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.y.h.lmb, ∀ c < X.y.fo.NC * 2 ^ (X.y.fo.kT + 5 - X.y.h.lmb),
      ν (.cell r c) = cellMW (T (2 * g)) i.mat (.cell (G.iB X.y) r c)) :
    ThreeFacts X.y.fo (G.kvG { X.layers with tokv := t } g (cellMW (T (2 * g)) i.mat))
      (fun u j => G.bitsG X.y (cellMW (T (2 * g)) i.mat) (u * 32 + j)) X.y.h.lmb ν := by
  rw [kvG_tokv]
  exact facts_layers Q M L hg ν hν

/-- Under the premises of claimsZero_layers, for every t: ClaimsZero with the key vectors
G.kvG { X.layers with tokv := t } g. -/
theorem claimsZero_layers_run (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T)
    (t : Array ℕ) {g : ℕ} (hg : g < 12) (jLK : ℕ) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.y.h.lmb, ∀ c < X.y.fo.NC * 2 ^ (X.y.fo.kT + 5 - X.y.h.lmb),
      ν (.cell r c) = cellMW (T (2 * g)) i.mat (.cell (G.iB X.y) r c))
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several X.y.fo = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits X.y.fo.v X.y.fo.d 5) :
    ClaimsZero X.y.fo X.y.h.lmb jLK
      (G.kvG { X.layers with tokv := t } g (cellMW (T (2 * g)) i.mat)) θ al ν C := by
  rw [kvG_tokv]
  exact claimsZero_layers Q M L hg jLK ν hν h0 θ al h1 C hC

/-- If X.hS.T = 1,024, R.h = X.hS, R.L = X.HLy and Hd.ReqFits holds of R and x: H.kvH at
Hd.pubH R (borderOf X.y) X.layers.wsLay is H.kvH at pubHAt X x, at every reading. -/
theorem kvH_run (hT : X.hS.T = 1024) (pl : AcceptancePolicy) (R : Head.Run) (hh : R.h = X.hS)
    (hL : R.L = X.HLy) (Rq : Hd.ReqFits R HeadSizes.ref (Head.Req.of pl x))
    (cell : H.NameH → Cb.Gl.E) :
    H.kvH (Hd.pubH R (borderOf X.y) X.layers.wsLay) cell = H.kvH (pubHAt X x) cell := by
  have h0 : 0 < (pubHAt X x).h.T := by
    have e : (pubHAt X x).h.T = 1024 := hT
    omega
  rw [pubH_run x R hh hL]
  exact kvH_agree (pubHAt X x) h0 (agreeCov_of_reqFits hT pl Rq) cell

/-- Under the premises of facts_head and of kvH_run: ThreeFacts with the key vectors
H.kvH (Hd.pubH R (borderOf X.y) X.layers.wsLay). -/
theorem facts_head_run (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T)
    (hT : X.hS.T = 1024) (pl : AcceptancePolicy) (R : Head.Run) (hh : R.h = X.hS) (hL : R.L = X.HLy)
    (Rq : Hd.ReqFits R HeadSizes.ref (Head.Req.of pl x)) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (T 24) i.mat (.cell (X.hS.NHf + 2) r c)) :
    ThreeFacts X.HLy.fs (H.kvH (Hd.pubH R (borderOf X.y) X.layers.wsLay) (readH (T 24) i.mat))
      (fun u j => H.bitsH X.hS X.HLy.fs (readH (T 24) i.mat) (u * 32 + j)) X.hS.lmbH ν := by
  rw [kvH_run hT pl R hh hL Rq]
  exact facts_head Q M L ν hν

/-- Under the premises of claimsZero_head and of kvH_run: ClaimsZero with the key vectors
H.kvH (Hd.pubH R (borderOf X.y) X.layers.wsLay). -/
theorem claimsZero_head_run (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T)
    (hT : X.hS.T = 1024) (pl : AcceptancePolicy) (R : Head.Run) (hh : R.h = X.hS) (hL : R.L = X.HLy)
    (Rq : Hd.ReqFits R HeadSizes.ref (Head.Req.of pl x)) (jLK : ℕ) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (T 24) i.mat (.cell (X.hS.NHf + 2) r c))
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several X.HLy.fs = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits X.HLy.fs.v X.HLy.fs.d 5) :
    ClaimsZero X.HLy.fs X.hS.lmbH jLK
      (H.kvH (Hd.pubH R (borderOf X.y) X.layers.wsLay) (readH (T 24) i.mat)) θ al ν C := by
  rw [kvH_run hT pl R hh hL Rq]
  exact claimsZero_head Q M L jLK ν hν h0 θ al h1 C hC

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.facts_layers_run
#print axioms OnBytes.HonestTrace.claimsZero_layers_run
#print axioms OnBytes.HonestTrace.kvH_run
#print axioms OnBytes.HonestTrace.facts_head_run
#print axioms OnBytes.HonestTrace.claimsZero_head_run
