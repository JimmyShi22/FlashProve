-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/FullPlanesRun.lean

What the lookups' key vectors, tables and planes of a layers' sub-proof and of the output head do
not read of the public data; so the statements of Johnson/HonestTrace/FullPlanes.lean, which stand
at X.layers and at pubHAt X x, hold at { X.layers with tokv := t } for every t, and at the head at
Hd.pubH of every value R of Head.Run that fits the request (Hd.ReqFits).

Why. publicOf's X.layers holds no request's tokens; a run of the Lean verifier under OnBytes/Model/
works with { X.layers with tokv := t }. pubHAt X x has the covered positions Hd.covReq x, in which
three of five fields (tokv, hWin, hRC) are placeholders, and for the checked tokens x.w at all 1,024
positions; by a reading of Head.coveredOf (OnBytes/Model/HeadLayout.lean) and Head.winOf
(OnBytes/Model/HeadHeard.lean) a run's checked token is 0 at a position that is not covered.
PlanesLaid, midP_layers and midP_head are stated at X.layers and pubHAt X x.

Main definitions and theorems:
* "kvG_tokv", "keyG_tokv", "tabG_tokv", "bG_tokv", "laidB_tokv": G.kvG, G.keyG, G.tabG, bG and LaidB
  at { P with tokv := t } are those at P, for every P and t. (G.bitsG takes P.y alone.)
* "AgreeCov P c' w'": at every position t below T the fields hOn and hOnC of c' have P.cov's values,
  and where t is covered w' has P.win's token.
* "segH_agree", "kvH_agree", "keyH_agree", "bH_agree", "laidBH_agree": if T is positive, under
  AgreeCov P c' w': H.kvH, H.keyH, bH and LaidBH at { P with cov := c', win := w' } are those at P.
  "tabH_agree": H.tabH too, for every c' and w'.
* "pubH_run": for a value R of Head.Run with R.h = X.hS and R.L = X.HLy, Hd.pubH R (borderOf X.y)
  X.layers.wsLay is pubHAt X x with R.cov and R.x.win laid in. "agreeCov_of_reqFits": if X.hS.T =
  1,024 and Hd.ReqFits (Johnson/Road/HeadLines.lean) holds of R and the request x, AgreeCov holds of
  pubHAt X x, R.cov and R.x.win.
* "laidB_run", "midP_layers_run": under the premises of midP_layers (for the first: PlanesLaid
  alone), LaidB and Cb.Lkp.MidP at { X.layers with tokv := t }, for every t.
* "laidBH_run", "midP_head_run": under the premises of midP_head (for the first: PlanesLaid alone)
  and X.hS.T = 1,024, for R with R.h = X.hS, R.L = X.HLy and Hd.ReqFits of R and x: LaidBH and
  Cb.Lkp.MidP at Hd.pubH R (borderOf X.y) X.layers.wsLay.

Limits. The layers' equations hold by definition. The head's do not: H.affH and H.gamH
(OnBytes/Tie/Pv/Lookup/Ends/H.lean) multiply what they read of the checked tokens by H.real, which
is 0 at a position that is not covered. Attention's terms take no such public data (A.kvA reads a
shape and a lookup's shape). Hd.ReqFits asks the covered and the counted positions below 1,024 and,
at covered positions alone, the checked token. That a run of the Lean verifier has R.h = X.hS, R.L =
X.HLy and Hd.ReqFits at a request on bytes is not shown in this file, nor X.hS.T = 1,024.

Not claimed: that the key vectors, tables and bits of OnBytes/Tie/Pv/Lookup/Ends/G.lean and
OnBytes/Tie/Pv/Lookup/Ends/H.lean are what the Lean verifier computes or tests; anything on a
prover, a claim, a round or a message.

-/
import Johnson.HonestTrace.FullPlanes

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
open OnBytes.Ends.H (NameH PubH)

/-! ## The layers: the request's tokens are not read -/

section Layers
variable {K : Type} [Field K]

/-- G.kvG at { P with tokv := t } is G.kvG at P. -/
theorem kvG_tokv (P : Layer.Pub) (t : Array ℕ) (g : ℕ) (cell : G.NameG → K) :
    G.kvG { P with tokv := t } g cell = G.kvG P g cell := rfl

/-- G.keyG at { P with tokv := t } is G.keyG at P. -/
theorem keyG_tokv (P : Layer.Pub) (t : Array ℕ) (g : ℕ) (cell : G.NameG → K) (θ : K) :
    G.keyG { P with tokv := t } g cell θ = G.keyG P g cell θ := rfl

/-- G.tabG at { P with tokv := t } is G.tabG at P. -/
theorem tabG_tokv (P : Layer.Pub) (t : Array ℕ) (θ : K) :
    G.tabG { P with tokv := t } θ = G.tabG P θ := rfl

/-- bG at { P with tokv := t } is bG at P. -/
theorem bG_tokv [DecidableEq K] (P : Layer.Pub) (t : Array ℕ) (g : ℕ) (cell : G.NameG → K) :
    bG { P with tokv := t } g cell = bG P g cell := rfl

/-- LaidB at { P with tokv := t } is LaidB at P. -/
theorem laidB_tokv [DecidableEq K] (P : Layer.Pub) (t : Array ℕ) (g : ℕ) (cell : G.NameG → K) :
    LaidB { P with tokv := t } g cell ↔ LaidB P g cell := Iff.rfl

end Layers

/-! ## The head: what is read of the covered positions and of the checked tokens -/

section Head
variable {K : Type} [Field K]

/-- c' and w' agree with P's covered positions and checked tokens as far as the key vectors read
them: at every position t below T the fields hOn and hOnC have P.cov's values, and where t is
covered w' has P.win's token. -/
def AgreeCov (P : PubH) (c' : Head.Covered) (w' : Array ℕ) : Prop :=
  ∀ t < P.h.T, c'.hOn.getD t false = P.cov.hOn.getD t false ∧
    c'.hOnC.getD t false = P.cov.hOnC.getD t false ∧
    (P.cov.hOn.getD t false = true → w'.getD t 0 = P.win.getD t 0)

/-- If at the position t the fields hOn and hOnC of c' have P.cov's values, and w' has P.win's token
if t is covered, then H.segH at { P with cov := c', win := w' } and at P have one value at t. -/
theorem segH_agree (P : PubH) (c' : Head.Covered) (w' : Array ℕ) (cell : NameH → K) {t : ℕ}
    (h1 : c'.hOn.getD t false = P.cov.hOn.getD t false)
    (h2 : c'.hOnC.getD t false = P.cov.hOnC.getD t false)
    (h3 : P.cov.hOn.getD t false = true → w'.getD t 0 = P.win.getD t 0) (sn : String) (x : ℕ) :
    H.segH { P with cov := c', win := w' } cell sn x t = H.segH P cell sn x t := by
  have hr : ∀ v, (H.real { P with cov := c', win := w' } v t : K) = H.real P v t := fun v => by
    show H.ind (c'.hOn.getD t false && decide (v < P.h.V)) = _
    rw [h1]
    rfl
  have hm : ∀ v, H.midK { P with cov := c', win := w' } cell v t = H.midK P cell v t := fun v => by
    show H.d1 P cell v t + 32896 * H.real { P with cov := c', win := w' } v t = _
    rw [hr]
    rfl
  have hl : ∀ v, H.lowK { P with cov := c', win := w' } cell v t = H.lowK P cell v t := fun v => by
    show H.d2 P cell v t + 128 * H.real { P with cov := c', win := w' } v t = _
    rw [hr]
    rfl
  have hw1 : (H.real P x t : K) * H.ind (decide (x < w'.getD t 0)) =
      H.real P x t * H.ind (decide (x < P.win.getD t 0)) := by
    by_cases hc : P.cov.hOn.getD t false = true
    · rw [h3 hc]
    · have r0 : (H.real P x t : K) = 0 := by
        unfold H.real H.ind
        simp [hc]
      rw [r0, zero_mul, zero_mul]
  have hw2 : (H.real P x t : K) * (H.lg P cell (w'.getD t 0) t - H.lg P cell x t) =
      H.real P x t * (H.lg P cell (P.win.getD t 0) t - H.lg P cell x t) := by
    by_cases hc : P.cov.hOn.getD t false = true
    · rw [h3 hc]
    · have r0 : (H.real P x t : K) = 0 := by
        unfold H.real H.ind
        simp [hc]
      rw [r0, zero_mul, zero_mul]
  have ea : H.affH { P with cov := c', win := w' } cell sn x t = H.affH P cell sn x t := by
    show (if sn == "NF" then
        2 ^ (P.h.KF - 1) - 2 ^ P.h.KF * H.aw P cell x t - 2 ^ 16 * (32896 + H.ra P cell x t)
      else if sn == "NFH" then 2 ^ (32 - P.h.KF) * (32896 + H.ra P cell x t)
      else if sn == "HD0" then
        H.iw P * (H.ind (decide (x < P.h.V) && c'.hOnC.getD t false) *
              (H.costC P cell t + 2 ^ 37 * H.costB P cell t) -
            H.real { P with cov := c', win := w' } x t * H.ind (decide (x < w'.getD t 0)) -
            2 ^ P.h.digSh * H.midK { P with cov := c', win := w' } cell x t -
            H.lowK { P with cov := c', win := w' } cell x t)
      else if sn == "HD1" then H.midK { P with cov := c', win := w' } cell x t
      else if sn == "HD2" then H.lowK { P with cov := c', win := w' } cell x t
      else if sn == "HE0" || sn == "HE1" then
        H.midK { P with cov := c', win := w' } cell (Head.firstEntry P.L sn + x) t +
          2 ^ 16 * ((Head.offE : ℕ) + H.ex P cell (Head.firstEntry P.L sn + x) t)
      else if sn == "ROW" then
        ((if x < ledNR P.h.XL then ledMu P.h.XL x else 1 : ℕ) : K) * H.dig P cell x t
      else if sn == "CNF" then
        H.aw P cell x t + 2 ^ 28 * H.nrm P cell x t + 2 ^ 15 + 2 ^ 39
      else 0) = _
    rw [hr, hm, hl, hm, h2, hw1]
    rfl
  have eg : H.gamH { P with cov := c', win := w' } cell sn x t = H.gamH P cell sn x t := by
    show (if sn == "NF" then H.recip P cell t * H.xs P cell x t
      else if sn == "HD0" then
        H.iw P * (H.real { P with cov := c', win := w' } x t *
          (H.lg P cell (w'.getD t 0) t - H.lg P cell x t))
      else 0) = _
    rw [hr, hw2]
    rfl
  show H.affH { P with cov := c', win := w' } cell sn x t +
    H.gamH { P with cov := c', win := w' } cell sn x t = _
  rw [ea, eg]
  rfl

/-- If T is positive, under AgreeCov P c' w': H.kvH at { P with cov := c', win := w' } is H.kvH at
P. -/
theorem kvH_agree (P : PubH) (hT : 0 < P.h.T) {c' : Head.Covered} {w' : Array ℕ}
    (A : AgreeCov P c' w') (cell : NameH → K) :
    H.kvH { P with cov := c', win := w' } cell = H.kvH P cell := by
  funext q i
  obtain ⟨h1, h2, h3⟩ := A (i % P.h.T) (Nat.mod_lt _ hT)
  show (match H.colH P.L q (i / P.h.T) with
    | some (sn, x) => H.segH { P with cov := c', win := w' } cell sn x (i % P.h.T)
    | none => ((tauN P.L.fs q (t0N P.L.fs q) : ℕ) : K)) =
    match H.colH P.L q (i / P.h.T) with
    | some (sn, x) => H.segH P cell sn x (i % P.h.T)
    | none => ((tauN P.L.fs q (t0N P.L.fs q) : ℕ) : K)
  cases H.colH P.L q (i / P.h.T) with
  | none => rfl
  | some a => exact segH_agree P c' w' cell h1 h2 h3 a.1 a.2

/-- If T is positive, under AgreeCov P c' w': H.keyH at { P with cov := c', win := w' } is H.keyH at
P. -/
theorem keyH_agree (P : PubH) (hT : 0 < P.h.T) {c' : Head.Covered} {w' : Array ℕ}
    (A : AgreeCov P c' w') (cell : NameH → K) (θ : K) :
    H.keyH { P with cov := c', win := w' } cell θ = H.keyH P cell θ := by
  show jointKey P.L.fs (H.kvH { P with cov := c', win := w' } cell) θ = _
  rw [kvH_agree P hT A]
  rfl

/-- H.tabH at { P with cov := c', win := w' } is H.tabH at P, for every c' and w'. -/
theorem tabH_agree (P : PubH) (c' : Head.Covered) (w' : Array ℕ) (θ : K) :
    H.tabH { P with cov := c', win := w' } θ = H.tabH P θ := rfl

/-- If T is positive, under AgreeCov P c' w': bH at { P with cov := c', win := w' } is bH at P. -/
theorem bH_agree [DecidableEq K] (P : PubH) (hT : 0 < P.h.T) {c' : Head.Covered} {w' : Array ℕ}
    (A : AgreeCov P c' w') (cell : NameH → K) :
    bH { P with cov := c', win := w' } cell = bH P cell := by
  show (fun r col => plane P.L.fs P.h.lmbH (hitsOf P.L.fs (tabOf K P.L.fs)
    (H.kvH { P with cov := c', win := w' } cell) (padH P.h P.L)) r col) = _
  rw [kvH_agree P hT A]
  rfl

/-- If T is positive, under AgreeCov P c' w': LaidBH at { P with cov := c', win := w' } is LaidBH at
P. -/
theorem laidBH_agree [DecidableEq K] (P : PubH) (hT : 0 < P.h.T) {c' : Head.Covered}
    {w' : Array ℕ} (A : AgreeCov P c' w') (cell : NameH → K) :
    LaidBH { P with cov := c', win := w' } cell ↔ LaidBH P cell := by
  show (∀ r < 2 ^ P.h.lmbH, ∀ c < P.L.fs.NC * 2 ^ (P.L.fs.kT + 5 - P.h.lmbH),
    cell (.cell (P.h.NHf + 2) r c) = (bH { P with cov := c', win := w' } cell r c : K)) ↔ _
  rw [bH_agree P hT A]
  exact Iff.rfl

end Head

/-! ## At the full size -/

section Full
variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- For a value R of Head.Run with R.h = X.hS and R.L = X.HLy: Hd.pubH R (borderOf X.y)
X.layers.wsLay is pubHAt X x with R.cov for its covered positions and R.x.win for its checked
tokens. -/
theorem pubH_run (x : Instance ppref) (R : Head.Run) (hh : R.h = X.hS) (hL : R.L = X.HLy) :
    Hd.pubH R (borderOf X.y) X.layers.wsLay =
      { pubHAt X x with cov := R.cov, win := R.x.win } := by
  unfold Hd.pubH pubHAt
  rw [hh, hL]

/-- If X.hS.T = 1,024 and Hd.ReqFits holds of R and the request x (the covered and the counted
positions below 1,024 are the request's, and at a covered position the checked token is the
request's), then AgreeCov holds of pubHAt X x, R.cov and R.x.win. -/
theorem agreeCov_of_reqFits (hT : X.hS.T = 1024) (pl : AcceptancePolicy) {R : Head.Run}
    (Rq : Hd.ReqFits R HeadSizes.ref (Head.Req.of pl x)) :
    AgreeCov (pubHAt X x) R.cov R.x.win := by
  intro t ht
  have ht' : t < HeadSizes.ref.T := by
    have e : (pubHAt X x).h.T = 1024 := hT
    rw [e] at ht
    exact ht
  have Q := Hd.reqFits_runReq (runAt X) pl x
  have a1 := (Rq.rho t ht').symm.trans (Q.rho t ht')
  have a2 := (Rq.rhoC t ht').symm.trans (Q.rhoC t ht')
  have b1 : R.cov.hOn.getD t false = (Hd.covReq x).hOn.getD t false := by
    have e : (Hd.runReq (runAt X) x).cov.hOn = (Hd.covReq x).hOn := rfl
    rw [e] at a1
    cases h : R.cov.hOn.getD t false <;> cases h' : (Hd.covReq x).hOn.getD t false <;>
      simp [h, h'] at a1 ⊢
  have b2 : R.cov.hOnC.getD t false = (Hd.covReq x).hOnC.getD t false := by
    have e : (Hd.runReq (runAt X) x).cov.hOnC = (Hd.covReq x).hOnC := rfl
    rw [e] at a2
    cases h : R.cov.hOnC.getD t false <;> cases h' : (Hd.covReq x).hOnC.getD t false <;>
      simp [h, h'] at a2 ⊢
  refine ⟨b1, b2, fun hc => ?_⟩
  have c1 := Rq.win t ht' (b1.trans hc)
  have c2 := Q.win t ht' hc
  exact c1.symm.trans c2

/-- Under PlanesLaid X i x T, for g below 12 and every t: LaidB holds at
{ X.layers with tokv := t } and the reading of list 2 g of T. -/
theorem laidB_run (L : PlanesLaid X i x T) (t : Array ℕ) {g : ℕ} (hg : g < 12) :
    LaidB { X.layers with tokv := t } g (cellMW (T (2 * g)) i.mat) :=
  (laidB_tokv X.layers t g _).2 (L.layers g hg)

/-- Under LookPub X, MeetsAll X i x T and PlanesLaid X i x T, for g below 12, every t and all θ and
al of Cb.Gl.E: Cb.Lkp.MidP holds of the joint key vector and the joint table at
{ X.layers with tokv := t }, the public padding and the planes' bits of the group g of layers, with
the keys and the bits read from list 2 g of T. -/
theorem midP_layers_run (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T)
    (t : Array ℕ) {g : ℕ} (hg : g < 12) (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP X.y.fo.v X.y.fo.d 5 32
      (G.keyG { X.layers with tokv := t } g (cellMW (T (2 * g)) i.mat) θ)
      (G.tabG { X.layers with tokv := t } θ) (FoNums.pads X.y.fo)
      (fun u j => G.bitsG X.y (cellMW (T (2 * g)) i.mat) (u * 32 + j)) al := by
  rw [keyG_tokv, tabG_tokv]
  exact midP_layers Q M L hg θ al

/-- Under PlanesLaid X i x T and X.hS.T = 1,024, for a value R of Head.Run with R.h = X.hS, R.L =
X.HLy and Hd.ReqFits of R and the request x: LaidBH holds at Hd.pubH R (borderOf X.y) X.layers.wsLay
and the reading of list 24 of T. -/
theorem laidBH_run (L : PlanesLaid X i x T) (hT : X.hS.T = 1024) (pl : AcceptancePolicy) (R : Head.Run)
    (hh : R.h = X.hS) (hL : R.L = X.HLy) (Rq : Hd.ReqFits R HeadSizes.ref (Head.Req.of pl x)) :
    LaidBH (Hd.pubH R (borderOf X.y) X.layers.wsLay) (readH (T 24) i.mat) := by
  have h0 : 0 < (pubHAt X x).h.T := by
    have e : (pubHAt X x).h.T = 1024 := hT
    omega
  rw [pubH_run x R hh hL]
  exact (laidBH_agree (pubHAt X x) h0 (agreeCov_of_reqFits hT pl Rq) _).2 L.head

/-- Under LookPub X, MeetsAll X i x T, PlanesLaid X i x T and X.hS.T = 1,024, for a value R of
Head.Run with R.h = X.hS, R.L = X.HLy and Hd.ReqFits of R and the request x, and all θ and al of
Cb.Gl.E: Cb.Lkp.MidP holds of the joint key vector and the joint table at Hd.pubH R (borderOf X.y)
X.layers.wsLay, the public padding and the planes' bits of the head, with the keys and the bits read
from list 24 of T. -/
theorem midP_head_run (Q : LookPub X) (M : MeetsAll X i x T) (L : PlanesLaid X i x T)
    (hT : X.hS.T = 1024) (pl : AcceptancePolicy) (R : Head.Run) (hh : R.h = X.hS) (hL : R.L = X.HLy)
    (Rq : Hd.ReqFits R HeadSizes.ref (Head.Req.of pl x)) (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP X.HLy.fs.v X.HLy.fs.d 5 32
      (H.keyH (Hd.pubH R (borderOf X.y) X.layers.wsLay) (readH (T 24) i.mat) θ)
      (H.tabH (Hd.pubH R (borderOf X.y) X.layers.wsLay) θ) (FoNums.pads X.HLy.fs)
      (fun u j => H.bitsH X.hS X.HLy.fs (readH (T 24) i.mat) (u * 32 + j)) al := by
  have h0 : 0 < (pubHAt X x).h.T := by
    have e : (pubHAt X x).h.T = 1024 := hT
    omega
  rw [pubH_run x R hh hL, keyH_agree (pubHAt X x) h0 (agreeCov_of_reqFits hT pl Rq), tabH_agree]
  exact midP_head Q M L θ al

end Full

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.kvG_tokv
#print axioms OnBytes.HonestTrace.keyG_tokv
#print axioms OnBytes.HonestTrace.tabG_tokv
#print axioms OnBytes.HonestTrace.bG_tokv
#print axioms OnBytes.HonestTrace.laidB_tokv
#print axioms OnBytes.HonestTrace.segH_agree
#print axioms OnBytes.HonestTrace.kvH_agree
#print axioms OnBytes.HonestTrace.keyH_agree
#print axioms OnBytes.HonestTrace.tabH_agree
#print axioms OnBytes.HonestTrace.bH_agree
#print axioms OnBytes.HonestTrace.laidBH_agree
#print axioms OnBytes.HonestTrace.pubH_run
#print axioms OnBytes.HonestTrace.agreeCov_of_reqFits
#print axioms OnBytes.HonestTrace.laidB_run
#print axioms OnBytes.HonestTrace.midP_layers_run
#print axioms OnBytes.HonestTrace.laidBH_run
#print axioms OnBytes.HonestTrace.midP_head_run
