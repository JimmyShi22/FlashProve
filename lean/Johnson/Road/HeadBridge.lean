-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadBridge.lean: one theorem in which the cells are those of the verifier's matrices,
the tables are the verifier's tables, and the keys are those of which the verifier's forms speak.

The files beside this one show, each for itself: where the verifier's forms take a cell to stand
(Johnson/Road/HeadPlace.lean); that the verifier's table of a lookup call is the library's
(Johnson/Road/HeadTabs.lean); that the form of a call's key vector is worth the extension of a
function on the call's columns with the library's keys in them (Johnson/Road/HeadCallLib.lean); and
that statements on such functions give the library's relation (Johnson/Road/HeadSum.lean). In
Johnson/Road/HeadSum.lean the cells, the tables and the keys are free letters. Here they are bound:
  the cells are cellsH, read in integer matrices Mz by the verifier's rule;
  the keys are kvOf at these cells, the keys of Johnson/Road/HeadCallLib.lean, with the program's
    own inverse of 2^(sh + 15) as the factor of the third digit of a margin;
  the padding key of a call is the reading of the row t0 of the verifier's table;
  "a row of the call's table" is the reading of a row of the verifier's table.

Main theorems: rows_of_port (a reading of a row of the verifier's table is an entry of the
library's table for the call's kind); callsFit_port; plainRF_of_port; reply_of_rf;
next_token_of_port.

What is not claimed. The statements on the functions, the identities and the entries are
hypotheses; no theorem derives them from a verifier's acceptance. So is what the layers must give.
HasAll and the marks' return are public facts on the layout, taken as hypotheses here. The theorem
goes by the cells: it does not use the places of the library's matrices. The program does not import
this file.
-/
import Johnson.Road.HeadSumP
import Johnson.Road.HeadSumMet
import Johnson.Road.HeadCallSum
import Johnson.Road.HeadPoint

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model Inst.Model.Head
open OnBytes.Model (Reading)

/-- The call that stands for a number beyond the list has no column. -/
theorem default_J : (default : Model.CallD).J = 0 := rfl

/-- In a layout that the verifier's function returns, at F = 24, sh = 8, sT = 4: for a call with a
column, the reading of a row of the verifier's table is an entry of the library's table for the
call's kind. -/
theorem rows_of_port {K : Type} [Field K] {ρ : Reading K} (hρ : Numerals ρ)
    {R : Model.Head.Run} (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hF : R.h.famF = 24)
    (hs : R.h.digSh = 8) (hT : R.h.tabS = 4) {q j : ℕ}
    (hj : j < (R.L.calls.getD q default).J) {u : ℕ} (hu : u < 2 ^ (R.L.cl.getD q default).k) :
    InLut (tabL R q) (ρ.val (ofF ((R.L.cl.getD q default).tauAt u))) := by
  have hq : q < R.L.calls.size := by
    by_contra hn
    have e : R.L.calls.getD q default = default := by
      simp [Array.getD, hn]
    rw [e, default_J] at hj
    exact absurd hj (Nat.not_lt_zero j)
  have hq' : q < R.L.cl.size := by
    rw [(clN_of_layout hy).1]
    exact hq
  have e1 : R.L.cl[q]? = some (R.L.cl.getD q default) := by
    simp [Array.getD, hq']
  obtain ⟨cd, hcd, _, hl⟩ := isLut_of_layout hy hF hs hT e1
  have e2 : R.L.calls.getD q default = cd := by
    have e3 : R.L.calls[q]? = some (R.L.calls.getD q default) := by
      simp [Array.getD, hq]
    rw [e3] at hcd
    exact Option.some.inj hcd
  unfold tabL
  rw [e2]
  exact hl.inLut hρ hu

/-- What Johnson/Road/HeadSum.lean asks of layout, keys and tables holds of the keys of
Johnson/Road/HeadCallLib.lean and the library's tables for the calls' kinds, for a request without a
counted position. -/
theorem callsFit_port {K : Type} [Field K] {R : Model.Head.Run} (Hs : HasAll R) (c : K)
    (np : NormPar) (t : Head.Cells K) (H : ℕ → ℕ → K) {y : Req}
    (h0 : ∀ i, i < 1024 → y.rhoC i = 0) :
    CallsFit R (kvOf c HeadSizes.ref np t H y) (tabL R) c np t H y :=
  callsFit_of c np t H h0 fun f => by
    obtain ⟨q, g, h1, h2, h3, h4⟩ := Hs f
    refine ⟨q, g, h1, h2, h3, ?_⟩
    unfold tabL
    rw [h4]
    exact lutOf_kindP f

/-- The field relation of the library's plain head, over the challenge field, at the cells read in
the integer matrices Mz: from the same statements as in next_token_of_port below, without what the
layers must give. -/
theorem plainRF_of_port {R : Model.Head.Run}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hF : R.h.famF = 24) (hs : R.h.digSh = 8)
    (hT : R.h.tabS = 4) (Hs : HasAll R) (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023)
    {Mz : Mats ℤ} {w : ℕ → Array ℕ} {fn : ℕ → ℕ → ℕ → Cb.Gl.E}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (Kf : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J
      (kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h)
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
        (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x))
      (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) (fn q))
    (small : ∀ a r c, |Mz a r c| < 2 ^ 18)
    (keys : ∀ q j, j < (R.L.calls.getD q default).J → ∀ a, a < nT →
      ∃ u, u < 2 ^ (R.L.cl.getD q default).k ∧
        fn q j a = Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt u)))
    (idns : ∀ a < nT, ∀ k < 17, Cm.Plain.idn (npOf R.h)
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) a k = 0) :
    Cm.Plain.TP.RF (F := Cb.Gl.E) (npOf R.h) (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E))
      (Cm.reqOf x) (cellsH R.h R.L R.b Mz) := by
  have h2 : (2 : Cb.Gl.E) ≠ 0 := by
    obtain ⟨c, hc⟩ := Down.exists_inv23 (K := Cb.Gl.E) (p := Cb.Gl.p)
      (algebraMap Cb.Gl.F Cb.Gl.E) (by have h := Down.gl_big; omega)
    intro h0
    rw [h0, zero_pow (by decide), mul_zero] at hc
    exact zero_ne_one hc
  have hc := iw_23 gl_numerals gl_inverse h2 hs
  have h0 : ∀ a, a < 1024 → (Cm.reqOf x).rhoC a = 0 := fun a _ =>
    HeadReq.rhoC_of_le (y := Cm.reqOf x) (le_of_eq hr.symm) a
  exact plainRF_of_calls hc (tz := cellsH R.h R.L R.b Mz)
    (callsFit_port Hs _ (npOf R.h) _ _ h0) hw Kf (small_cellsH R.h R.L R.b small)
    (fun q j hj a ha => by
      obtain ⟨u, hu, e⟩ := keys q j hj a ha
      rw [e]
      exact rows_of_port gl_numerals hy hF hs hT hj hu)
    idns

/-- From the field relation over the challenge field, with what the layers must give, to the
library's relation of a request for the next token. -/
theorem reply_of_rf {κ : ℕ → LayerScale} {nf : NormPar} {tbs : ℕ → Tables} (hn : nf.OK)
    (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023) (he : x.e = 1024)
    {tz : Head.Cells ℤ}
    (rf : Cm.Plain.TP.RF (F := Cb.Gl.E) nf (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E))
      (Cm.reqOf x) tz)
    (hl : Top.LayersGive κ tbs i.val x.prompt tz) (pol : AcceptancePolicy) : RinfR ppref κ nf tbs pol i x :=
  haveI : Cm.TI.Big Cb.Gl.p := Down.big_gl
  Top.next_token_of_head (p := Cb.Gl.p) hn i x hr he hl (Down.plainRF_gl.1 rf) pol

/-- **From the verifier's matrices, tables and key functions to the reply.** R: a run whose layout
is what the verifier's function returns, at F = 24, sh = 8, sT = 4. Mz: integer matrices, one for
each matrix of the sub-proof's list. For a request for the next token (r = 1,023, e = 1,024), let
fn q be a function on the columns of call q and the positions that has, in the column of each entry
of each segment, the library's key at the cells read in Mz (the third digit of a margin times the
program's inverse of 2^23), and in each column without a mark the reading of the verifier's padding
key. If every entry of Mz is below 2^18 in absolute value, every value of every fn q is the reading
of a row of the verifier's table of call q, every identity of the final normalisation is 0 at these
cells, and the layers give what the head borrows, then the library's relation holds under every
policy: the integer program runs, and the reply is the least token of largest logit at the last
position. -/
theorem next_token_of_port {R : Model.Head.Run}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hF : R.h.famF = 24) (hs : R.h.digSh = 8)
    (hT : R.h.tabS = 4) (Hs : HasAll R) {κ : ℕ → LayerScale} {tbs : ℕ → Tables}
    (hn : (npOf R.h).OK) (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023)
    (he : x.e = 1024) {Mz : Mats ℤ} {w : ℕ → Array ℕ} {fn : ℕ → ℕ → ℕ → Cb.Gl.E}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (Kf : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J
      (kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h)
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
        (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x))
      (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) (fn q))
    (small : ∀ a r c, |Mz a r c| < 2 ^ 18)
    (keys : ∀ q j, j < (R.L.calls.getD q default).J → ∀ a, a < nT →
      ∃ u, u < 2 ^ (R.L.cl.getD q default).k ∧
        fn q j a = Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt u)))
    (idns : ∀ a < nT, ∀ k < 17, Cm.Plain.idn (npOf R.h)
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) a k = 0)
    (hl : Top.LayersGive κ tbs i.val x.prompt (cellsH R.h R.L R.b Mz)) (pol : AcceptancePolicy) :
    RinfR ppref κ (npOf R.h) tbs pol i x :=
  reply_of_rf hn i x hr he (plainRF_of_port hy hF hs hT Hs i x hr hw Kf small keys idns) hl pol

#print axioms rows_of_port
#print axioms callsFit_port
#print axioms plainRF_of_port
#print axioms next_token_of_port

end OnBytes.Road.Hd
