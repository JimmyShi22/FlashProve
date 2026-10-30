-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoHeadBDefs.lean.
The test on public numbers under the head's key forms: the definitions alone.

Fo.headB2 is one test of the head's shape, its layout and the plan's list of matrices, made for
statements on the key forms of the head's lookup. No statement of this library asks it; one asks its
part segOnceB. This file holds that test and its parts and nothing else: no theorem, and no import
but the byte-level verifier's own files and the file with the lookup's public numbers. So the test
can be evaluated at a layout without the proofs.

Defines:
  segOnceB L qN qH: the segments NF and HD0 stand in the calls qN and qH alone.
  hfB h L mats: each part of the matrix hf has the layout's rows and columns in the list; a part's
    rows are whole blocks of 2^la rows.
  slB h L q g OFF nl J: at a use of Head.Sl: S2 divides the segment's length and each limb's first
    feature; each block of S2 entries stands in S2 neighbouring columns from a multiple of S2 on;
    the blocks' columns lie among the call's; the tensor's blocks lie in the table.
  slUses h L sn: the uses that Head.LINE makes of Head.Sl at the segment sn.
  rowB, cnfB, hrB: the tests at the segments ROW and CNF and at the matrix hr.
  segB, callB: the tests at a segment and at a call.
  headB, headB2: the tests at a head; headB2 is the whole.
What the tests give: OnBytes/Tie/Pv/Lookup/Forest/FoAlgH.lean (segOnce_of_test).

-/
import OnBytes.Model.HeadHeard
import OnBytes.Tie.Pv.Lookup.Ends.Joint

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Ends

/-- The test of SegOnce on the layout. -/
def segOnceB (L : Head.HL) (qN qH : ℕ) : Bool :=
  (List.range L.calls.size).all fun q => (L.calls.getD q default).segs.all fun g =>
    (g.name != "NF" || q == qN) && (g.name != "HD0" || q == qH)

/-- The test on the matrix hf. -/
def hfB (h : Head.Shape) (L : Head.HL) (mats : Array TMat) : Bool :=
  ((List.range h.NHf).all fun p => (mats.getD p {}).m == L.m && (mats.getD p {}).k == L.k) &&
    L.m == L.m / 2 ^ h.la * 2 ^ h.la

/-- The test at a use of Head.Sl. -/
def slB (h : Head.Shape) (L : Head.HL) (q : ℕ) (g : Seg) (OFF nl J : ℕ) : Bool :=
  g.n == h.S2 * (g.n / h.S2) &&
    ((List.range nl).all fun l => OFF + l * J == h.S2 * ((OFF + l * J) / h.S2)) &&
    ((List.range (g.n / h.S2)).all fun xh => (List.range h.S2).all fun c2 =>
      g.pos.getD (h.S2 * xh + c2) 0 == h.S2 * (g.pos.getD (h.S2 * xh) 0 / h.S2) + c2) &&
    ((List.range (g.n / h.S2)).all fun xh =>
      decide (g.pos.getD (h.S2 * xh) 0 / h.S2 < 2 ^ ((L.calls.getD q default).lJ - h.ls))) &&
    ((List.range nl).all fun l =>
      decide ((OFF + l * J) / h.S2 + g.n / h.S2 ≤ h.NHf * (L.k * (L.m / 2 ^ h.la))))

/-- The uses that Head.LINE makes of Head.Sl at a segment. -/
def slUses (h : Head.Shape) (L : Head.HL) (sn : String) : List (ℕ × ℕ × ℕ) :=
  if sn == "NF" then [(L.oAw, 2, h.d), (L.oRa, 2, h.d)]
  else if sn == "NFH" then [(L.oRa, 2, h.d)]
  else if sn == "HD0" then [(L.oD1, 2, L.JV), (L.oD2, 1, L.JV)]
  else if sn == "HD1" then [(L.oD1, 2, L.JV)]
  else if sn == "HD2" then [(L.oD2, 1, L.JV)]
  else if sn == "HE0" || sn == "HE1" then
    [(L.oD1 + Head.firstEntry L sn, 2, L.JV), (L.oE + Head.firstEntry L sn, exc, L.JV)]
  else if sn == "CNF" then [(L.oAw, 2, h.d)]
  else []

/-- The test of Fo.RowFacts. -/
def rowB (h : Head.Shape) (L : Head.HL) (mats : Array TMat) (g : Seg) : Bool :=
  g.n == ledNRH h.XL && (mats.getD (h.NHf + 1) {}).m == L.mR &&
    (mats.getD (h.NHf + 1) {}).k == L.kR && decide (ledNRH h.XL ≤ L.kR * (L.mR / h.T))

/-- The test of Fo.CnfFacts. -/
def cnfB (h : Head.Shape) (L : Head.HL) (mats : Array TMat) (g : Seg) : Bool :=
  g.n == h.d && (mats.getD h.NHf {}).m == L.mD && (mats.getD h.NHf {}).k == L.kD &&
    decide (2 * h.d ≤ L.kD * (L.mD / h.T))

/-- The test on the matrix hr. -/
def hrB (h : Head.Shape) (L : Head.HL) (mats : Array TMat) : Bool :=
  (mats.getD (h.NHf + 1) {}).m == L.mR && (mats.getD (h.NHf + 1) {}).k == L.kR &&
    decide (ledNRH h.XL ≤ L.kR * (L.mR / h.T))

/-- The test at a segment. -/
def segB (h : Head.Shape) (L : Head.HL) (mats : Array TMat) (q : ℕ) (g : Seg) : Bool :=
  ["NF", "NFH", "HD0", "HD1", "HD2", "HE0", "HE1", "ROW", "CNF"].contains g.name &&
    Head.callNo L g.name == some q && g.pos.size == g.n &&
    ((slUses h L g.name).all fun u => slB h L q g u.1 u.2.1 u.2.2) &&
    (g.name != "ROW" || rowB h L mats g) && (g.name != "CNF" || cnfB h L mats g)

/-- The test at a call. -/
def callB (h : Head.Shape) (L : Head.HL) (q : ℕ) : Bool :=
  decide (((L.calls.getD q default).segs.map (·.name)).Nodup) &&
    (L.calls.getD q default).J == 2 ^ (L.calls.getD q default).lJ &&
    (L.cl.getD q default).n == (L.calls.getD q default).lJ + h.lt &&
    tauN L.fs q (t0N L.fs q) == ((L.cl.getD q default).tauAt (L.cl.getD q default).t0).toNat &&
    ((L.calls.getD q default).segs.map fun g => if g.name = "HD0" then 1 else 0).sum ==
      (if Head.callNo L "HD0" = some q then 1 else 0)

/-- **The test at a head.** -/
def headB (h : Head.Shape) (L : Head.HL) (mats : Array TMat) : Bool :=
  hfB h L mats &&
    ((List.range L.cl.size).all fun q =>
      callB h L q && (L.calls.getD q default).segs.all (segB h L mats q)) &&
    (match Head.callNo L "NF", Head.callNo L "HD0" with
      | some a, some b => segOnceB L a b
      | _, _ => false)

/-- **The test at a head, whole.** -/
def headB2 (h : Head.Shape) (L : Head.HL) (mats : Array TMat) : Bool :=
  headB h L mats && hrB h L mats

end Fo
