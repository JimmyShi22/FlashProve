-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookAtRunFo.lean

The head's statements of Johnson/HonestTrace/LookAtRun.lean at two further forms of the head's
public data: Fo.pubH R lay (OnBytes/Tie/Pv/Lookup/Ends/FoKeysH.lean), whose border is R.b, and
Fo.Pub2.pubHAt X cov win (OnBytes/Tie/Pv/Lookup/Ends/FoLookPubHX.lean).

Main theorems:
* "foPubH_eq": if R.b = borderOf X.y: Fo.pubH R X.layers.wsLay = Hd.pubH R (borderOf X.y)
  X.layers.wsLay.
* "pub2_eq": Fo.Pub2.pubHAt X c' w' = { pubHAt X x with cov := c', win := w' }, for every x.
* "kvH_foRun": if X.hS.T = 1,024, R.h = X.hS, R.L = X.HLy, R.b = borderOf X.y and Hd.ReqFits R
  HeadSizes.ref (Head.Req.of pl x): H.kvH (Fo.pubH R X.layers.wsLay) cell = H.kvH (pubHAt X x) cell.
* "kvH_pub2": if X.hS.T = 1,024 and AgreeCov (pubHAt X x) c' w': H.kvH (Fo.Pub2.pubHAt X c' w') cell
  = H.kvH (pubHAt X x) cell.
* "facts_head_foRun", "claimsZero_head_foRun", "facts_head_pub2", "claimsZero_head_pub2": under
  LookPub X, MeetsAll X i x T, PlanesLaid X i x T, the premises of kvH_foRun or of kvH_pub2, and the
  premises on ν (and on θ and C) of facts_head and claimsZero_head: ThreeFacts and ClaimsZero with
  these key vectors.

Limits. One rewriting each. R.b = borderOf X.y, R.h = X.hS, R.L = X.HLy, Hd.ReqFits, AgreeCov and
X.hS.T = 1,024 are premises; none is shown here of a run. The limits of
Johnson/HonestTrace/LookAtRun.lean hold here.

Not claimed: that a verifier accepts the rounds; anything on a prover's program.

-/
import Johnson.HonestTrace.LookAtRun
import OnBytes.Tie.Pv.Lookup.Ends.FoKeysH
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubHX

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Model OnBytes.Ends
open OnBytes.Model.Verify (borderOf)
open OnBytes.Road
open OnBytes.Road.Hd (readH)
open Look

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- If R.b = borderOf X.y: Fo.pubH R at X's layout of the weights is Hd.pubH R at borderOf X.y and
that layout. -/
theorem foPubH_eq (R : Head.Run) (hb : R.b = borderOf X.y) :
    _root_.Fo.pubH R X.layers.wsLay = Hd.pubH R (borderOf X.y) X.layers.wsLay := by
  unfold _root_.Fo.pubH Hd.pubH
  rw [hb]

/-- Fo.Pub2.pubHAt X c' w' is pubHAt X x with c' and w' laid in, for every x. -/
theorem pub2_eq (x : Instance ppref) (c' : Head.Covered) (w' : Array ℕ) :
    _root_.Fo.Pub2.pubHAt X c' w' = { pubHAt X x with cov := c', win := w' } := rfl

/-- If X.hS.T = 1,024, R.h = X.hS, R.L = X.HLy, R.b = borderOf X.y and Hd.ReqFits holds of R at
HeadSizes.ref and Head.Req.of pl x: H.kvH at Fo.pubH R X.layers.wsLay is H.kvH at pubHAt X x, at
every reading. -/
theorem kvH_foRun (hT : X.hS.T = 1024) (pl : AcceptancePolicy) (R : Head.Run) (hh : R.h = X.hS)
    (hL : R.L = X.HLy) (hb : R.b = borderOf X.y)
    (Rq : Hd.ReqFits R HeadSizes.ref (Head.Req.of pl x)) (cell : H.NameH → Cb.Gl.E) :
    H.kvH (_root_.Fo.pubH R X.layers.wsLay) cell = H.kvH (pubHAt X x) cell := by
  rw [foPubH_eq R hb]
  exact kvH_run hT pl R hh hL Rq cell

/-- If X.hS.T = 1,024 and AgreeCov (pubHAt X x) c' w': H.kvH at Fo.Pub2.pubHAt X c' w' is H.kvH at
pubHAt X x, at every reading. -/
theorem kvH_pub2 (hT : X.hS.T = 1024) {c' : Head.Covered} {w' : Array ℕ}
    (A : AgreeCov (pubHAt X x) c' w') (cell : H.NameH → Cb.Gl.E) :
    H.kvH (_root_.Fo.Pub2.pubHAt X c' w') cell = H.kvH (pubHAt X x) cell := by
  have h0 : 0 < (pubHAt X x).h.T := by
    have e : (pubHAt X x).h.T = 1024 := hT
    omega
  rw [pub2_eq x c' w']
  exact kvH_agree (pubHAt X x) h0 A cell

/-- Under the premises of facts_head and of kvH_foRun: ThreeFacts with the key vectors H.kvH
(Fo.pubH R X.layers.wsLay). -/
theorem facts_head_foRun (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T)
    (hT : X.hS.T = 1024) (pl : AcceptancePolicy) (R : Head.Run) (hh : R.h = X.hS) (hL : R.L = X.HLy)
    (hb : R.b = borderOf X.y) (Rq : Hd.ReqFits R HeadSizes.ref (Head.Req.of pl x))
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (T 24) i.mat (.cell (X.hS.NHf + 2) r c)) :
    ThreeFacts X.HLy.fs (H.kvH (_root_.Fo.pubH R X.layers.wsLay) (readH (T 24) i.mat))
      (fun u j => H.bitsH X.hS X.HLy.fs (readH (T 24) i.mat) (u * 32 + j)) X.hS.lmbH ν := by
  rw [kvH_foRun hT pl R hh hL hb Rq]
  exact facts_head Q M L ν hν

/-- Under the premises of claimsZero_head and of kvH_foRun: ClaimsZero with the key vectors H.kvH
(Fo.pubH R X.layers.wsLay). -/
theorem claimsZero_head_foRun (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T)
    (hT : X.hS.T = 1024) (pl : AcceptancePolicy) (R : Head.Run) (hh : R.h = X.hS) (hL : R.L = X.HLy)
    (hb : R.b = borderOf X.y) (Rq : Hd.ReqFits R HeadSizes.ref (Head.Req.of pl x)) (jLK : ℕ)
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (T 24) i.mat (.cell (X.hS.NHf + 2) r c))
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several X.HLy.fs = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits X.HLy.fs.v X.HLy.fs.d 5) :
    ClaimsZero X.HLy.fs X.hS.lmbH jLK
      (H.kvH (_root_.Fo.pubH R X.layers.wsLay) (readH (T 24) i.mat)) θ al ν C := by
  rw [kvH_foRun hT pl R hh hL hb Rq]
  exact claimsZero_head Q M L jLK ν hν h0 θ al h1 C hC

/-- Under the premises of facts_head and of kvH_pub2: ThreeFacts with the key vectors H.kvH
(Fo.Pub2.pubHAt X c' w'). -/
theorem facts_head_pub2 (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T)
    (hT : X.hS.T = 1024) {c' : Head.Covered} {w' : Array ℕ} (A : AgreeCov (pubHAt X x) c' w')
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (T 24) i.mat (.cell (X.hS.NHf + 2) r c)) :
    ThreeFacts X.HLy.fs (H.kvH (_root_.Fo.Pub2.pubHAt X c' w') (readH (T 24) i.mat))
      (fun u j => H.bitsH X.hS X.HLy.fs (readH (T 24) i.mat) (u * 32 + j)) X.hS.lmbH ν := by
  rw [kvH_pub2 hT A]
  exact facts_head Q M L ν hν

/-- Under the premises of claimsZero_head and of kvH_pub2: ClaimsZero with the key vectors H.kvH
(Fo.Pub2.pubHAt X c' w'). -/
theorem claimsZero_head_pub2 (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T)
    (hT : X.hS.T = 1024) {c' : Head.Covered} {w' : Array ℕ} (A : AgreeCov (pubHAt X x) c' w')
    (jLK : ℕ) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (T 24) i.mat (.cell (X.hS.NHf + 2) r c))
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several X.HLy.fs = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits X.HLy.fs.v X.HLy.fs.d 5) :
    ClaimsZero X.HLy.fs X.hS.lmbH jLK
      (H.kvH (_root_.Fo.Pub2.pubHAt X c' w') (readH (T 24) i.mat)) θ al ν C := by
  rw [kvH_pub2 hT A]
  exact claimsZero_head Q M L jLK ν hν h0 θ al h1 C hC

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.foPubH_eq
#print axioms OnBytes.HonestTrace.pub2_eq
#print axioms OnBytes.HonestTrace.kvH_foRun
#print axioms OnBytes.HonestTrace.kvH_pub2
#print axioms OnBytes.HonestTrace.facts_head_foRun
#print axioms OnBytes.HonestTrace.claimsZero_head_foRun
#print axioms OnBytes.HonestTrace.facts_head_pub2
#print axioms OnBytes.HonestTrace.claimsZero_head_pub2
