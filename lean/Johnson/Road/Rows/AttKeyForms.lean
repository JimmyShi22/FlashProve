-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttKeyForms.lean: the key forms that the verifier of an attention sub-proof makes
are the library's key forms at the hidden values under the slots.

The verifier makes the key form of each of its four calls from terms, one for each unit or segment
(OnBytes/Model/AttentionClaimsA.lean, OnBytes/Model/AttentionClaimsB.lean: keyKR, padTerm, keyKFD,
keyWL, keyIX, keyWH). The library writes the four key forms as functions KF of the values of the
named scalars (Inst/Model/Att/KeyForms.lean). This file shows, term by term, that the value of the
verifier's form in a world is the library's expression at the hidden values under the slots.

Main theorems.
 - sumW_value: the sum of the pieces' weights.
 - idOf_value, leOf_value: the verifier's extension of the number of an index, and of the relation
   "at most", read as the library's idP and LE.
 - indexForm_value: the index as a form on its bits.
 - keyKR_value, keyKFD_fm, keyKFD_fd, remForm_value, keyWL_value, keyIX_value, keyWH_value: the
   terms. The padding's term of a call of kind KFD (padTerm) is a public constant and has no lemma
   here.

What is taken as given in each: what the public numbers in the term read as (the sums of the
pieces' weights). What is not claimed: that the routines which put the terms together (callKR,
callKFD, joinR16) return these sums of terms; that the slots are those of the named scalars; what
the numbers of the shift and the padding key are. Nothing is said about probabilities or about
hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttRows14

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff ofNat scaleNat)
open OnBytes.Attention (PW PlaneClaim Score Divide ShD Seg Shape sumW onesOf idOf leOf keyKR keyKFD
  remForm indexForm keyWL keyIX keyWH eqPair)
open Inst.Model.AttSeg (idP LE ones eq1 sh)

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-! ## Public numbers -/

/-- A sum that is folded from the left. -/
theorem foldl_add {α : Type} (g : α → E) (l : List α) (a : E) :
    ρ.val (l.foldl (fun s x => addE s (g x)) a) = ρ.val a + (l.map fun x => ρ.val (g x)).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, ρ.add, List.map_cons, List.sum_cons, add_assoc]

/-- The sum of the pieces' weights. -/
theorem sumW_value (pw : Array PW) :
    ρ.val (sumW pw) = (pw.toList.map fun x => ρ.val x.wp).sum := by
  unfold sumW
  rw [← Array.foldl_toList, foldl_add ρ (fun x : PW => x.wp), ρ.zero, zero_add]

variable {ρ}

/-- The verifier's extension of the number of an index reads as the library's. -/
theorem idOf_value (hρ : Numerals ρ) (z : Array E) : ρ.val (idOf z) = idP z.size (pt ρ z) := by
  unfold idOf idP
  rw [foldl_add ρ (fun v => scaleNat (z.getD v zeroE) (2 ^ (z.size - 1 - v))), ρ.zero, zero_add,
    sum_map_range]
  refine sum_congr rfl fun k _ => ?_
  rw [hρ.scaleNat, Nat.cast_pow, Nat.cast_ofNat]
  rfl

variable (ρ)

/-- The fold of leOf over the coordinates from v on. -/
theorem leFold_value (x y : Array E) : ∀ (n v : ℕ),
    ρ.val (((List.range' v n).reverse).foldl (fun le w =>
      addE (mulE (subE oneE (x.getD w zeroE)) (y.getD w zeroE))
        (mulE (eqPair (x.getD w zeroE) (y.getD w zeroE)) le)) oneE) =
      LE n (sh (pt ρ x) v) (sh (pt ρ y) v)
  | 0, _ => by simp [Inst.Model.AttSeg.LE, ρ.one]
  | n + 1, v => by
    rw [List.range'_succ, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ρ.add, ρ.mul, ρ.mul, ρ.sub, ρ.one, eqPair_value, leFold_value x y n (v + 1)]
    show _ = (1 - sh (pt ρ x) v 0) * sh (pt ρ y) v 0 +
      eq1 (sh (pt ρ x) v 0) (sh (pt ρ y) v 0) * LE n (sh (sh (pt ρ x) v) 1) (sh (sh (pt ρ y) v) 1)
    have e : ∀ u : ℕ → K, sh (sh u v) 1 = sh u (v + 1) := fun u => by
      funext t
      unfold sh
      rw [Nat.add_assoc]
    rw [e, e]
    simp only [sh, Nat.add_zero]
    rfl

/-- The verifier's extension of the relation "at most" reads as the library's. -/
theorem leOf_value (x y : Array E) : ρ.val (leOf x y) = LE x.size (pt ρ x) (pt ρ y) := by
  have h := leFold_value ρ x y x.size 0
  have e : ∀ u : ℕ → K, sh u 0 = u := fun u => by
    funext t
    unfold sh
    rw [Nat.zero_add]
  rw [e, e, ← List.range_eq_range'] at h
  exact h

variable {ρ}

/-! ## The terms -/

/-- The index as a form on its bits. -/
theorem indexForm_value (hρ : Numerals ρ) (d : Divide) (lt : ℕ) :
    (indexForm d lt).value ρ W = ∑ k ∈ range lt, (2 : K) ^ k * W.slot (d.sIB + k) := by
  unfold indexForm
  have key : ∀ (l : List ℕ) (a : Aff),
      (l.foldl (fun s k => Aff.addMul s (Aff.slot (d.sIB + k)) (ofNat (2 ^ k))) a).value ρ W =
        a.value ρ W + (l.map fun k => (2 : K) ^ k * W.slot (d.sIB + k)).sum := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons k l ih =>
      intro a
      rw [List.foldl_cons, ih, Aff.value_addMul, Aff.value_slot, hρ.ofNat, Nat.cast_pow,
        Nat.cast_ofNat, List.map_cons, List.sum_cons, add_assoc]
  rw [key, Aff.value_ofConst, ρ.zero, zero_add, sum_map_range]

/-- What a unit adds to the key form of a call of kind KR. LW: what the sum of its pieces' weights
reads as. -/
theorem keyKR_value (hρ : Numerals ρ) (pc : PlaneClaim) {LW : K} (hL : ρ.val (sumW pc.pw) = LW) :
    (keyKR pc).value ρ W =
      (W.slot pc.s0 + 128 * LW) + 2 ^ 20 * (W.slot (pc.s0 + 1) + 128 * LW) +
        2 ^ 40 * W.slot (pc.s0 + 2) := by
  unfold keyKR
  simp only [Aff.value_add, Aff.value_scale, Aff.value_slot, Aff.value_ofConst, hρ.scaleNat,
    hρ.ofNat, hL]
  push_cast
  ring

/-- What the unit below the diagonal adds to the key form of a call of kind KFD. -/
theorem keyKFD_fm (hρ : Numerals ρ) (d : ShD) (k : Score) (hk : k.seg = Seg.fm) {LW : K}
    (hL : ρ.val (sumW k.pw) = LW) :
    (keyKFD d k).value ρ W =
      (W.slot (k.s0 + 5) - W.slot (k.s0 + 6) + (d.C : K) * LW * ones k.zs.size (pt ρ k.zs)) -
        (W.slot k.s0 + 128 * LW) - 256 * (W.slot (k.s0 + 1) + 128 * LW) +
        2 ^ 32 * W.slot (k.s0 + 2) +
        2 ^ 33 * (W.slot (k.s0 + 3) + 128 * LW + 256 * W.slot (k.s0 + 4)) := by
  unfold keyKFD
  simp only [hk, beq_self_eq_true, if_true, Aff.value_add, Aff.value_sub, Aff.value_scale,
    Aff.value_slot, Aff.value_ofConst, hρ.scaleNat, hρ.ofNat, ρ.mul, onesOf_value, hL]
  push_cast
  ring

/-- What the unit on the diagonal adds to the key form of a call of kind KFD. -/
theorem keyKFD_fd (hρ : Numerals ρ) (d : ShD) (k : Score) (hk : k.seg = Seg.fd) {LW : K}
    (hL : ρ.val (sumW k.pw) = LW) :
    (keyKFD d k).value ρ W =
      (W.slot (k.s0 + 5) - W.slot (k.s0 + 6) +
          (d.Om : K) * LW * (1 - LE k.zj.size (pt ρ k.zj) (pt ρ k.zi))) -
        (W.slot k.s0 + 128 * LW) - 256 * (W.slot (k.s0 + 1) + 128 * LW) +
        2 ^ 32 * W.slot (k.s0 + 2) +
        2 ^ 33 * (W.slot (k.s0 + 3) + 128 * LW + 256 * W.slot (k.s0 + 4)) := by
  have hne : (Seg.fd == Seg.fm) = false := rfl
  unfold keyKFD
  simp only [hk, hne, Bool.false_eq_true, if_false, Aff.value_add, Aff.value_sub, Aff.value_scale,
    Aff.value_slot, Aff.value_ofConst, hρ.scaleNat, hρ.ofNat, ρ.mul, ρ.sub, ρ.one, leOf_value, hL]
  push_cast
  ring

/-- The form REM. -/
theorem remForm_value (hρ : Numerals ρ) (d : Divide) :
    (remForm d).value ρ W = 2 * W.slot d.sACC + W.slot d.sZC - 2 * W.slot d.sZO := by
  unfold remForm
  simp only [Aff.value_add, Aff.value_sub, Aff.value_scale, Aff.value_slot, hρ.ofNat]
  push_cast
  ring

/-- The term of segment wl. -/
theorem keyWL_value (hρ : Numerals ρ) (d : Divide) {LW : K} (hL : ρ.val (sumW d.pwW) = LW) :
    (keyWL d).value ρ W =
      (1 - ρ.val d.zsl) * ((2 * W.slot d.sACC + W.slot d.sZC - 2 * W.slot d.sZO) -
          2 ^ 16 * (W.slot d.sRH + 128 * LW)) +
        ρ.val d.zsl * (2 * W.slot d.sZC - LW -
          (2 * W.slot d.sACC + W.slot d.sZC - 2 * W.slot d.sZO) -
          2 ^ 16 * (W.slot d.sRHP + 128 * LW)) := by
  unfold keyWL
  simp only [Aff.value_add, Aff.value_sub, Aff.value_scale, Aff.value_slot, Aff.value_ofConst,
    remForm_value W hρ, hρ.scaleNat, hρ.ofNat, ρ.sub, ρ.one, hL]
  push_cast
  ring

/-- The term of segment ix. -/
theorem keyIX_value (hρ : Numerals ρ) (S : Shape) (d : Divide) {LW : K}
    (hL : ρ.val (sumW d.pwX) = LW) :
    (keyIX S d).value ρ W =
      2 ^ (16 - S.cf.lt) * (LW * idP d.ziX.size (pt ρ d.ziX) -
        ∑ k ∈ range S.cf.lt, (2 : K) ^ k * W.slot (d.sIB + k)) := by
  unfold keyIX
  simp only [Aff.value_sub, Aff.value_scale, Aff.value_ofConst, indexForm_value W hρ, hρ.ofNat,
    ρ.mul, idOf_value hρ, hL]
  push_cast
  ring

/-- The key form of the call of kind WH. -/
theorem keyWH_value (hρ : Numerals ρ) (d : Divide) {LW : K} (hL : ρ.val (sumW d.pwH) = LW) :
    (keyWH d).value ρ W =
      (W.slot d.s5h + 128 * LW) + 2 ^ 20 * (W.slot (d.s5h + 1) + 128 * LW) := by
  unfold keyWH
  simp only [Aff.value_add, Aff.value_scale, Aff.value_slot, Aff.value_ofConst, hρ.scaleNat,
    hρ.ofNat, hL]
  push_cast
  ring

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.leOf_value
#print axioms OnBytes.Road.Rows.keyKFD_fm
#print axioms OnBytes.Road.Rows.keyKFD_fd
#print axioms OnBytes.Road.Rows.keyWL_value
#print axioms OnBytes.Road.Rows.keyIX_value
