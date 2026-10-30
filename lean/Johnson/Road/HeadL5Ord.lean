-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadL5Ord.lean: "the head's link is in order", said call by call, as the verifier's
layout lays the head's lookup; keys and identities are the library's, written with the sizes as
letters; and that, at the library's sizes, it gives the statement HeadOrd of
Johnson/Road/HeadL5.lean.

HeadOrd speaks of the library's keys and tables, which are written for the library's sizes alone.
The verifier's lookup for the head speaks of something else: of calls, each with columns and a table
of its own. OrdPort says it so: every entry of the matrices is small; in each call, every value in
every column at every position is a row of that call's table, where a column of a segment holds the
segment's keys at the cells that are read in the matrices, and a column of no segment the call's
padding key; and the 17 identities of the final normalisation are 0 at every position. Keys and
identities are those of Johnson/Road/HeadSizes.lean and Johnson/Road/HeadCallLib.lean (kvOf), which
are written for any sizes z. Nothing in OrdPort is a hidden value of a sub-proof, a challenge or a
claim: it reads the shape, the layout, the record of the stream's cells, the matrices, the output
matrix and the request.

Main definition: OrdPort.
Main theorem: ord_of_ordPort: at the library's sizes, for a request with r = 1,023 (then the
request's mark rhoC of a counted position is 0 everywhere: rhoC_of_le in Johnson/Road/HeadReq.lean),
OrdPort gives HeadOrd.

What is not claimed. Nothing derives OrdPort from a proof file. At other sizes than the library's
OrdPort is a definition and no more: no theorem says what follows from it there. The keys of the two
families that the plain head does not have (HE0, HE1) and the last 21 bytes of ROW are asked to be
rows of their tables too; HeadOrd does not ask that. The program does not import this file.
-/
import Johnson.Road.HeadL5
import Johnson.Road.HeadBridge
import Johnson.Road.HeadCallsLaid

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model (ppref NormPar Instance Mat Index)
open Inst.Model.Head (nT nD nV Req)
open Inst.Model.All (DF)
open OnBytes.Model (Reading)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Verify (borderOf)

/-- The head's link is in order, said call by call. R: a record of a run, of which the shape,
the layout and the record of the stream's cells alone are read. z: the sizes. H: the output matrix.
yq: what the head reads of the request. Mz: the integer matrices of the head's list. -/
def OrdPort (R : Model.Head.Run) (z : HeadSizes.Sizes) (H : ℕ → ℕ → Cb.Gl.E) (yq : Req)
    (Mz : Mats ℤ) : Prop :=
  (∀ a r c, |Mz a r c| < 2 ^ 18) ∧
  (∀ q w fn, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some w →
    KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J
      (kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) z (npOf R.h)
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) H yq)
      (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) fn →
    ∀ j, j < (R.L.calls.getD q default).J → ∀ a, a < z.T →
      ∃ u, u < 2 ^ (R.L.cl.getD q default).k ∧
        fn j a = Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt u))) ∧
  ∀ a < z.T, ∀ k < 17, HeadSizes.idn z (npOf R.h)
    (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) a k = 0

/-- **At the library's sizes OrdPort gives HeadOrd.** For a request with
r = 1,023. i: the index; Wz: digits in which the library's layout reads the output matrix of i. -/
theorem ord_of_ordPort {R : Model.Head.Run} {hy' : Model.Layer.Shape} {pc : List (List String)}
    {y : Lay} (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h)
    (hF : R.h.famF = 24) (hs : R.h.digSh = 8) (hT : R.h.tabS = 4)
    (hl : Model.Layer.layout hy' pc = .ok y) (S : Switches hy') (Z : Sized hy' DF)
    (Z2 : Sized2 hy' DF) (hb : R.b = borderOf y) (i : Index ppref) (x : Instance ppref)
    (hr : x.r = 1023) {Wz : Mat}
    (hHz : ∀ j < nD, ∀ v < nV,
      i.val.H j v = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H j v)
    {Mz : Mats ℤ}
    (O : OrdPort R HeadSizes.ref (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x) Mz) :
    HeadOrd R.h R.L y (npOf R.h) Wz x Mz := by
  obtain ⟨small, keys, idns⟩ := O
  choose w hw using marks_of_layout (R := R) hy
  have Hs : HasAll R := hasAll_of_layout hy hFull.lt hFull.d hFull.V hFull.XL
  choose fn Kf using fun q => exists_keyFn (hw q)
    (kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h)
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x))
    (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0)))
  have rf := plainRF_of_port hy hF hs hT Hs i x hr hw Kf small
    (fun q j hj a ha => keys q (w q) (fn q) (hw q) (Kf q) j hj a ha) idns
  rw [hb] at rf
  exact ord_of_rf hFull hy hl S Z Z2 hHz small rf

#print axioms ord_of_ordPort

end OnBytes.Road.Hd
