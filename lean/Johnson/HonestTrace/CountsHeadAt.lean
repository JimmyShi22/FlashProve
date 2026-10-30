-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsHeadAt.lean

lawH of Johnson/HonestTrace/CountsHead.lean at the library's reading of the output head's cells in
integer matrices, in the field Cb.Gl.E, with its premise on the keys taken from Hd.ForInH; and where
bH is 0.

Notation. R : Head.Run holds a shape R.h and a layout R.L; b, lay, Mh, Wz are arbitrary (b is an
argument of its own, not R's field of that name). Hd.pubH R b lay is what is public at the head:
R.h, R.L, b, R.cov, R.x.win and lay; and Hd.readH Mh Wz the reading of the names in the integer
matrices Mh and Wz, cast into Cb.Gl.E (Johnson/Road/Ends/HeadTies.lean). Hd.ForInH R K says that for
every call below NC every place of K below 2^(n_c) holds the value of a row below 2^(k_c) of the
call's table (Johnson/Road/Ends/HeadForIn.lean); Hd.callsH R b lay Mh Wz has the key vectors
Ends.H.kvH at that reading (Johnson/Road/Ends/HeadInSeam.lean). The rest: as in CountsHead.lean.

Main theorems:
* "kb_H": if Head.layout h tau returns L, L.kb = NC * 2^(kT + 5 - lmbH).
* "bH_outside", "bH_outside_kb": from row 2^lmbH on, and from column NC * 2^(kT + 5 - lmbH) on (if
  the layout returns: from column P.L.kb on), bH P cell is 0.
* "inTable_of_forInH": ForInH R (callsH R b lay Mh Wz).K gives lawH's premise on the keys at pubH R
  b lay and readH Mh Wz. The two unfold to one term, so the proof is the hypothesis itself.
* "lawH_forInH": lawH with that premise.
* "lawH_withBH": if Head.layout R.h tau returns R.L, R.L.JV = R.h.V and ForInH holds as above, then
  at every θ and al Cb.Lkp.MidP holds of the keys and the bits of one reading: readH Mh Wz with its
  bH laid over matrix number NHf + 2. No further premise on cells.

Limits. No theorem of this file shows ForInH of any matrices, that Head.layout returns for some
shape, or R.L.JV = R.h.V for some layout. lawH_withBH's reading is withBH of readH Mh Wz; that it is
readH of a list of integer matrices is not shown in this file.

Not claimed: that a prover's committed cells are these; that MidP makes any claim of the protocol's
lookup argument hold; that a verifier accepts a proof made with these cells; anything on soundness
or zero knowledge.

-/
import Johnson.HonestTrace.CountsHeadSkip
import Johnson.Road.Ends.HeadForIn

set_option autoImplicit false

namespace OnBytes.HonestTrace

open OnBytes.Model
open OnBytes.Ends.H (NameH PubH)
open OnBytes.Road.Hd (ForInH callsH pubH readH)

/-- If Head.layout h tau returns L, the field kb of L, the number of columns of the matrix bH, is NC
* 2^(kT + 5 - lmbH). -/
theorem kb_H {h : Head.Shape} {tau : Array F} {L : Head.HL} (hy : Head.layout h tau = .ok L) :
    L.kb = L.fs.NC * 2 ^ (L.fs.kT + 5 - h.lmbH) := by
  unfold Head.layout at hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨L0, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨cs, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨fs, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨kb, hk, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, hy⟩ := Road.Hd.ok_of_needed hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  cases hy
  unfold Forest.planeCols at hk
  split_ifs at hk
  exact (Except.ok.inj hk).symm

/-- From row 2^lmbH on and from column NC * 2^(kT + 5 - lmbH) on, bH P cell is 0, at every P and
every reading of the names in every field with decidable equality. -/
theorem bH_outside {K : Type} [Field K] [DecidableEq K] (P : PubH) (cell : NameH → K) {r c : ℕ}
    (ho : 2 ^ P.h.lmbH ≤ r ∨ P.L.fs.NC * 2 ^ (P.L.fs.kT + 5 - P.h.lmbH) ≤ c) :
    bH P cell r c = 0 :=
  plane_outside _ _ _ ho

/-- If Head.layout P.h tau returns P.L: from row 2^lmbH on and from column P.L.kb on, bH P cell is
0. -/
theorem bH_outside_kb {K : Type} [Field K] [DecidableEq K] {tau : Array F} (P : PubH)
    (hy : Head.layout P.h tau = .ok P.L) (cell : NameH → K) {r c : ℕ}
    (ho : 2 ^ P.h.lmbH ≤ r ∨ P.L.kb ≤ c) : bH P cell r c = 0 := by
  rw [kb_H hy] at ho
  exact plane_outside _ _ _ ho

/-- ForInH R (callsH R b lay Mh Wz).K gives the premise of lawH on the keys, at pubH R b lay, readH
Mh Wz and the field Cb.Gl.E. -/
theorem inTable_of_forInH {R : Head.Run} {b : Head.Border} {lay : WsLay} {Mh : Road.Mats ℤ}
    {Wz : Inst.Model.Mat} (H : ForInH R (callsH R b lay Mh Wz).K) :
    ∀ c < (pubH R b lay).L.fs.NC, Cb.Lkp.InTable (FoNums.nOf (pubH R b lay).L.fs c)
      (FoNums.kOf (pubH R b lay).L.fs c) (Ends.H.kvH (pubH R b lay) (readH Mh Wz) c)
      (tabOf Cb.Gl.E (pubH R b lay).L.fs c) := H

/-- If Head.layout R.h tau returns R.L, and ForInH R (callsH R b lay Mh Wz).K, FillerIsPad and
LaidBH hold at pubH R b lay and readH Mh Wz, then for all θ and al Cb.Lkp.MidP holds of the joint
key vector, the joint table, FoNums.pads R.L.fs and the planes' bits; keys and bits are both read at
readH Mh Wz. -/
theorem lawH_forInH {R : Head.Run} {tau : Array F} (hy : Head.layout R.h tau = .ok R.L)
    (b : Head.Border) (lay : WsLay) (Mh : Road.Mats ℤ) (Wz : Inst.Model.Mat)
    (H : ForInH R (callsH R b lay Mh Wz).K)
    (hfill : FillerIsPad (pubH R b lay) (readH Mh Wz))
    (hb : LaidBH (pubH R b lay) (readH Mh Wz)) (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP R.L.fs.v R.L.fs.d 5 32 (Ends.H.keyH (pubH R b lay) (readH Mh Wz) θ)
      (Ends.H.tabH (pubH R b lay) θ) (FoNums.pads R.L.fs)
      (fun u j => Ends.H.bitsH R.h R.L.fs (readH Mh Wz) (u * 32 + j)) al :=
  lawH (pubH R b lay) hy (readH Mh Wz) (inTable_of_forInH H) hfill hb θ al

/-- **Where JV = V, MidP follows from the layout and ForInH alone.** If Head.layout R.h tau
returns R.L, R.L.JV = R.h.V, and ForInH R (callsH R b lay Mh Wz).K holds, then for all θ and al
Cb.Lkp.MidP holds of the joint key vector, the joint table, FoNums.pads R.L.fs and the planes' bits;
keys and bits are both read at withBH (pubH R b lay) (readH Mh Wz). -/
theorem lawH_withBH {R : Head.Run} {tau : Array F} (hy : Head.layout R.h tau = .ok R.L)
    (hJV : R.L.JV = R.h.V) (b : Head.Border) (lay : WsLay) (Mh : Road.Mats ℤ)
    (Wz : Inst.Model.Mat) (H : ForInH R (callsH R b lay Mh Wz).K) (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP R.L.fs.v R.L.fs.d 5 32
      (Ends.H.keyH (pubH R b lay) (withBH (pubH R b lay) (readH Mh Wz)) θ)
      (Ends.H.tabH (pubH R b lay) θ) (FoNums.pads R.L.fs)
      (fun u j => Ends.H.bitsH R.h R.L.fs (withBH (pubH R b lay) (readH Mh Wz)) (u * 32 + j))
      al :=
  lawH (pubH R b lay) hy _
    (inTable_withBH _ _ (keysSkipBH (pubH R b lay) hy _) (inTable_of_forInH H))
    (fillerIsPad_of_JV (pubH R b lay) hy hJV _)
    (withBH_laid _ _ (keysSkipBH (pubH R b lay) hy _)) θ al

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.kb_H
#print axioms OnBytes.HonestTrace.bH_outside
#print axioms OnBytes.HonestTrace.bH_outside_kb
#print axioms OnBytes.HonestTrace.inTable_of_forInH
#print axioms OnBytes.HonestTrace.lawH_forInH
#print axioms OnBytes.HonestTrace.lawH_withBH
