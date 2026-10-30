-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttKeyAll.lean: the sums of terms that make up the verifier's four key forms of an
attention sub-proof are the library's four key forms at the hidden values under the slots.

Johnson/Road/Rows/AttKeyForms.lean values the terms. This file adds them up, call by call, and
holds the result against the library's KF (Inst/Model/Att/KeyForms.lean) at the values slotVal W h u
of the named scalars (Johnson/Road/Rows/AttBetween.lean).

Main definitions and theorems.
 - KeyPub: what the public numbers in the terms read as: the sums of the pieces' weights of the
   seven families; the points in three terms; the numbers C and Om of the shift; the padding's term.
 - kf0, kf1, kf2, kf3: under KeyPub, the value of the sum of the terms of a call is KF at that call.

What is not claimed. That KeyPub holds of a run: its fields are public facts. That the routines
which put the terms together (callKR, callKFD, joinR16) return these sums. Nothing is said about
probabilities or about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttKeyForms
import Johnson.Road.Rows.AttBetween

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff)
open OnBytes.Attention (Heard ShD Seg sumW keyKR keyKFD keyWL keyIX keyWH)
open Inst.Model (Scl)
open Inst.Model.AttSeg (Calls Pub KF DP REM LL ones idP zs zi' zj' zChi xi Om)

variable {K : Type} [Field K]

/-- What the public numbers in the terms of the key forms read as. sd: the numbers of the shift;
pad: the padding's term of the call of kind KFD. -/
structure KeyPub (ρ : Reading K) [scl : Scl] (h : Heard) (u : Units) (C : Calls) (p : Pub K)
    (sd : ShD) (pad : E) : Prop where
  num : Numerals ρ
  segM : u.kM.seg = Seg.fm
  segD : u.kD.seg = Seg.fd
  lt : h.S.cf.lt = (L5.dimOf h.S).lT
  m1 : ρ.val (sumW u.pM.pw) = LL (L5.dimOf h.S) C p.z .m1
  d1 : ρ.val (sumW u.pD.pw) = LL (L5.dimOf h.S) C p.z .d1
  m2 : ρ.val (sumW u.kM.pw) = LL (L5.dimOf h.S) C p.z .m2
  d2 : ρ.val (sumW u.kD.pw) = LL (L5.dimOf h.S) C p.z .d2
  w3 : ρ.val (sumW h.d.pwW) = LL (L5.dimOf h.S) C p.z .w3
  x3 : ρ.val (sumW h.d.pwX) = LL (L5.dimOf h.S) C p.z .x3
  f4 : ρ.val (sumW h.d.pwH) = LL (L5.dimOf h.S) C p.z .f4
  ones : Inst.Model.AttSeg.ones u.kM.zs.size (pt ρ u.kM.zs) =
    Inst.Model.AttSeg.ones ((L5.dimOf h.S).lP + 1) (zs (L5.dimOf h.S) C p.z)
  le : Inst.Model.AttSeg.LE u.kD.zj.size (pt ρ u.kD.zj) (pt ρ u.kD.zi) =
    Inst.Model.AttSeg.LE (L5.dimOf h.S).lB (zj' (L5.dimOf h.S) C p.z) (zi' (L5.dimOf h.S) C p.z)
  chi : ρ.val h.d.zsl = zChi (L5.dimOf h.S) C p.z
  id : idP h.d.ziX.size (pt ρ h.d.ziX) = idP (L5.dimOf h.S).lT (xi (L5.dimOf h.S) C p.z)
  cut : (sd.C : K) = (((L5.dimOf h.S).cutC : ℤ) : K)
  om : (sd.Om : K) = ((Om (L5.dimOf h.S) : ℤ) : K)
  pad : ρ.val pad = (1 - LL (L5.dimOf h.S) C p.z .m2 - LL (L5.dimOf h.S) C p.z .d2) *
    (((L5.dimOf h.S).cutC - 2 ^ (L5.dimOf h.S).sh + 2 ^ 32 : ℤ) : K)

variable {ρ : Reading K} [scl : Scl] {h : Heard} {u : Units} {C : Calls} {p : Pub K} {sd : ShD}
  {pad : E} (W : World K)

/-- The call of kind KR. -/
theorem kf0 (P : KeyPub ρ h u C p sd pad) :
    (Aff.ofConst zeroE + keyKR u.pM + keyKR u.pD).value ρ W =
      KF (L5.dimOf h.S) C p (slotVal W h u) 0 := by
  rw [Aff.value_add, Aff.value_add, Aff.value_ofConst, ρ.zero, keyKR_value W P.num u.pM P.m1,
    keyKR_value W P.num u.pD P.d1]
  simp only [KF]
  rw [sum_pair (by decide)]
  simp only [slotVal, slotOf, Nat.add_zero]
  ring

/-- The call of kind KFD. -/
theorem kf1 (P : KeyPub ρ h u C p sd pad) :
    (Aff.ofConst pad + keyKFD sd u.kM + keyKFD sd u.kD).value ρ W =
      KF (L5.dimOf h.S) C p (slotVal W h u) 1 := by
  rw [Aff.value_add, Aff.value_add, Aff.value_ofConst, P.pad, keyKFD_fm W P.num sd u.kM P.segM P.m2,
    keyKFD_fd W P.num sd u.kD P.segD P.d2, P.ones, P.le, P.cut, P.om]
  simp only [KF]
  rw [sum_pair (by decide)]
  simp only [DP, Inst.Model.AttSeg.Fam.reg, slotVal, slotOf, Nat.add_zero]
  ring

/-- The call of kind R16. -/
theorem kf2 (P : KeyPub ρ h u C p sd pad) :
    (Aff.ofConst zeroE + keyWL h.d + keyIX h.S h.d).value ρ W =
      KF (L5.dimOf h.S) C p (slotVal W h u) 2 := by
  rw [Aff.value_add, Aff.value_add, Aff.value_ofConst, ρ.zero, keyWL_value W P.num h.d P.w3,
    keyIX_value W P.num h.S h.d P.x3, P.chi, P.id, P.lt]
  simp only [KF, REM, slotVal, slotOf]
  ring

/-- The call of kind WH. -/
theorem kf3 (P : KeyPub ρ h u C p sd pad) :
    (keyWH h.d).value ρ W = KF (L5.dimOf h.S) C p (slotVal W h u) 3 := by
  rw [keyWH_value W P.num h.d P.f4]
  simp only [KF, slotVal, slotOf]

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.kf0
#print axioms OnBytes.Road.Rows.kf1
#print axioms OnBytes.Road.Rows.kf2
#print axioms OnBytes.Road.Rows.kf3
