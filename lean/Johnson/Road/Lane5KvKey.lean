-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5KvKey.lean

The keys of an attention sub-proof's lookup calls as segKey writes them over the verifier's own
records (OnBytes/Tie/Pv/Lookup/Ends/A.lean: a term written for this library) are the library's
looked-up values of an attention segment (Inst/Model/Att/Trace.lean: key1, key2, key3W, key3X,
key4) at the cells that stand in the verifier's matrices by the rule of Lane5AttDef.lean (addrA).
For every commutative ring, EVERY reading "cell" of A.lean's names (not only casts of integers),
every pair number b: segment by segment.

Main definitions and theorems:
* "tC S cell": the library's trace from a reading of A.lean's names: the cell of a library's name r
  is cell at the place addrA S r. "cellZ Z": the reading off integer matrices Z; "tC_cellZ": there
  tC is castT (cellsA S Z), by rfl.
* "NumsA S": the numbers of the shape that A.lean's terms read are the library's at "dimOf S": B,
  nT, hP, G, T, dh, lt; the four tensors of qa have two limbs; the bound on a score is the
  library's. Public. A premise here; a THEOREM for every shape that the verifier's own shape or
  shapeHid returns at ldh = 7 (Lane5KvNums.lean); a test with its theorem in Lane5KvCheck.lean.
* "asC_M", "asC_D", "mx_eq", "den_eq", "ib_eq", "ten_qry" .. "rhp_eq": cell by cell.
* "segKey_rm", "segKey_rd", "segKey_wh", "segKey_ix"; in Lane5KvKey2.lean: "segKey_fm",
  "segKey_fd", "segKey_wl".

At fm and fd the shift sh of the call must be the library's one shift (the first layer's).
Not claimed: how the keys are laid in a call (Lane5KvVec.lean); that the rule of addresses is the
program's.
-/
import Johnson.Road.Lane5AttDef
import OnBytes.Tie.Pv.Lookup.Ends.A
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Ends OnBytes.Ends.A Finset
open OnBytes.Attention (Seg)
open Inst.Model.AttSeg

variable {R : Type} [CommRing R]

/-- The reading of A.lean's names off the integer matrices of the link's list. -/
def cellZ (Z : Zs) (x : NameA) : R := ((Z x.M x.r x.c : ℤ) : R)

/-- A place (number in the list, row, column) as a name of A.lean. -/
def nmOf (a : ℕ × ℕ × ℕ) : NameA := ⟨a.1, a.2.1, a.2.2⟩

/-- **The library's trace from a reading of A.lean's names.** -/
def tC (S : Attention.Shape) (cell : NameA → R) : Raw → R := fun r => cell (nmOf (addrA S r))

/-- At integer matrices the trace is Lane5AttDef.lean's. -/
theorem tC_cellZ (S : Attention.Shape) (Z : Zs) :
    tC S (cellZ Z : NameA → R) = castT (cellsA S Z) := rfl

/-- sumN is the sum over the range. -/
theorem sumN_sum (n : ℕ) (f : ℕ → R) : sumN n f = ∑ i ∈ range n, f i := by
  have h : ∀ (l : List ℕ) (s : R), l.foldl (fun s i => s + f i) s = s + (l.map f).sum := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons x l ih =>
      intro s
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      ring
  unfold sumN
  rw [h, zero_add]
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- **The numbers of the shape that A.lean's terms read are the library's.** Public. -/
structure NumsA (S : Attention.Shape) : Prop where
  B : S.B = (dimOf S).B
  nT : S.nT = (dimOf S).nBlk
  hP : S.hP = (dimOf S).hP
  G : S.G = (dimOf S).nG
  T : S.T = (dimOf S).T
  dh : S.dh = (dimOf S).ch
  lt : S.cf.lt = (dimOf S).lT
  nlQ : S.atQ.nl = 2
  nlK : S.atK.nl = 2
  nlV : S.atV.nl = 2
  nlO : S.atO.nl = 2
  Sm : ((S.Smax : ℕ) : ℤ) = Inst.Model.Smax

variable (S : Attention.Shape) (cell : NameA → R)

/-! ## Cell by cell -/

theorem asC_M (jj b π : ℕ) :
    asC S cell jj (b / S.HA) (b % S.HA) false π = tC S cell (.c .M jj b π) := by
  simp only [asC, tC, nmOf, addrA, asCell, Bool.false_eq_true, if_false,
    Nat.zero_add]

theorem asC_D (jj b π : ℕ) :
    asC S cell jj (b / S.HA) (b % S.HA) true π = tC S cell (.c .D jj b π) := by
  simp only [asC, tC, nmOf, addrA, asCell, if_true]

theorem mx_eq (b g i : ℕ) :
    mx S cell (b / S.HA) (g * S.HA + b % S.HA) i = mxV (tC S cell) b g i := by
  unfold mx limbs mxV
  rw [sumN_sum]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  rfl

theorem den_eq (b g i : ℕ) :
    den S cell (b / S.HA) (g * S.HA + b % S.HA) i = denV (tC S cell) b g i := by
  unfold den limbs denV
  rw [sumN_sum]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  rfl

theorem ib_eq (k b g i : ℕ) :
    ib S cell (b / S.HA) k (g * S.HA + b % S.HA) i = ibV (tC S cell) k b g i := by
  simp only [ib, ibV, featC, tC, nmOf, addrA, featCell, Nat.zero_mul, Nat.zero_add,
    Nat.add_assoc]

theorem ten_qry (N : NumsA S) (b g i n : ℕ) :
    ten S cell S.atQ (b / S.HA) ((g * S.HA + b % S.HA) * S.dh + n) i =
      qryV (tC S cell) b g i n := by
  unfold ten limbs qryV
  rw [sumN_sum, N.nlQ]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  simp only [featC, tC, nmOf, addrA, featCell, Model.tenCell, Nat.add_assoc]

theorem ten_out (N : NumsA S) (b g i n : ℕ) :
    ten S cell S.atO (b / S.HA) ((g * S.HA + b % S.HA) * S.dh + n) i =
      outV (tC S cell) b g i n := by
  unfold ten limbs outV
  rw [sumN_sum, N.nlO]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  simp only [featC, tC, nmOf, addrA, featCell, Model.tenCell, Nat.add_assoc]

theorem ten_key (N : NumsA S) (lam g j n : ℕ) :
    ten S cell S.atK lam (g * S.dh + n) j = keyV (tC S cell) lam g j n := by
  unfold ten limbs keyV
  rw [sumN_sum, N.nlK]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  simp only [featC, tC, nmOf, addrA, featCell, Model.tenCell, Nat.add_assoc]

theorem ten_val (N : NumsA S) (lam g j n : ℕ) :
    ten S cell S.atV lam (g * S.dh + n) j = valV (tC S cell) lam g j n := by
  unfold ten limbs valV
  rw [sumN_sum, N.nlV]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  simp only [featC, tC, nmOf, addrA, featCell, Model.tenCell, Nat.add_assoc]

theorem rh_eq (b g i n : ℕ) :
    rh S cell (b / S.HA) ((g * S.HA + b % S.HA) * S.dh + n) i + 128 =
      qhV (tC S cell) b g i n := by
  simp only [rh, qhV, featC, tC, nmOf, addrA, featCell, Model.tenCell,
    Attention.atRh, Nat.zero_mul, Nat.zero_add, Nat.add_assoc]

theorem rhp_eq (b g i n : ℕ) :
    rhp S cell (b / S.HA) ((g * S.HA + b % S.HA) * S.dh + n) i + 128 =
      qhV' (tC S cell) b g i n := by
  simp only [rhp, qhV', featC, tC, nmOf, addrA, featCell, Model.tenCell,
    Attention.atRhp, Nat.zero_mul, Nat.zero_add, Nat.add_assoc]

/-! ## The segments without products -/

theorem segKey_rm (sh b κ : ℕ) :
    segKey S cell sh .rm (b / S.HA) (b % S.HA) κ = key1 (tC S cell) .M b κ := by
  show (asC S cell 0 (b / S.HA) (b % S.HA) false κ + 128) +
    ((2 ^ 20 : ℕ) : R) * (asC S cell 1 (b / S.HA) (b % S.HA) false κ + 128) +
    ((2 ^ 40 : ℕ) : R) * asC S cell 2 (b / S.HA) (b % S.HA) false κ = _
  rw [asC_M, asC_M, asC_M]
  unfold key1 r0 r1 flV
  push_cast
  ring

theorem segKey_rd (sh b κ : ℕ) :
    segKey S cell sh .rd (b / S.HA) (b % S.HA) κ = key1 (tC S cell) .D b κ := by
  show (asC S cell 0 (b / S.HA) (b % S.HA) true κ + 128) +
    ((2 ^ 20 : ℕ) : R) * (asC S cell 1 (b / S.HA) (b % S.HA) true κ + 128) +
    ((2 ^ 40 : ℕ) : R) * asC S cell 2 (b / S.HA) (b % S.HA) true κ = _
  rw [asC_D, asC_D, asC_D]
  unfold key1 r0 r1 flV
  push_cast
  ring

theorem segKey_wh (N : NumsA S) (sh b κ : ℕ) :
    segKey S cell sh .wh (b / S.HA) (b % S.HA) κ =
      key4 (tC S cell) b (κ / (dimOf S).ch / (dimOf S).T) (κ / (dimOf S).ch % (dimOf S).T)
        (κ % (dimOf S).ch) := by
  show (rh S cell (b / S.HA) ((κ / (S.dh * S.T) * S.HA + b % S.HA) * S.dh + κ % S.dh)
      (κ / S.dh % S.T) + 128) + ((2 ^ 20 : ℕ) : R) *
    (rhp S cell (b / S.HA) ((κ / (S.dh * S.T) * S.HA + b % S.HA) * S.dh + κ % S.dh)
      (κ / S.dh % S.T) + 128) = _
  rw [rh_eq, rhp_eq, ← Nat.div_div_eq_div_mul, N.dh, N.T]
  unfold key4
  push_cast
  ring

theorem segKey_ix (N : NumsA S) (sh b κ : ℕ) :
    segKey S cell sh .ix (b / S.HA) (b % S.HA) κ =
      key3X (dimOf S) (tC S cell) b (κ / (dimOf S).T) (κ % (dimOf S).T) := by
  show ((2 ^ (16 - S.cf.lt) : ℕ) : R) * (((κ % S.T : ℕ) : R) - sumN S.cf.lt fun k =>
    ((2 ^ k : ℕ) : R) * ib S cell (b / S.HA) k (κ / S.T * S.HA + b % S.HA) (κ % S.T)) = _
  rw [sumN_sum]
  simp only [ib_eq]
  rw [N.lt, N.T]
  unfold key3X
  push_cast
  rfl

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.segKey_rm
#print axioms OnBytes.Road.L5.segKey_wh
#print axioms OnBytes.Road.L5.segKey_ix
