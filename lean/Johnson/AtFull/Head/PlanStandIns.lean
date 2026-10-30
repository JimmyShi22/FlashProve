-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Head/PlanStandIns.lean: small stand-ins for the head's layout and for the owner's
plan, made of what Head.planH2 reads of them (headReads | ownerReads, PlanReads.lean beside):
numbers, and arrays of the right sizes with nothing in them. Definitions with code and two laws.
No sub-protocol imports this file.
  standL r          a layout with headReads (standL r) = r, for a list r of nineteen numbers
  OwnerW            the four things that are read of an owner, where all four are there: the label,
                    five numbers of the last array that another sub-proof reads, the sum of two
                    sizes, the owner's own entry for the stream
  OwnerW.reads      as ownerReads gives them
  standO w          an owner with ownerReads (standO w) = w.reads, where the sum is not 0 and the
                    entry is whole (PlaceF.whole)
Limits. A stand-in is no layout and no plan of anything: it serves planH2_congr alone. No soundness
is claimed. On hiding nothing.
-/
import Johnson.AtFull.Head.PlanReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Head
open OnBytes OnBytes.Model OnBytes.Model.Head

/-- A layout that holds the nineteen numbers and nothing else. -/
def standL (r : List Nat) : HL :=
  { fs := { calls := Array.replicate (r.getD 0 0) {}, pub := Array.replicate (r.getD 2 0) 0,
            NT := r.getD 3 0, dT := r.getD 4 0, rK := r.getD 5 0, kT := r.getD 6 0,
            cK := r.getD 7 0, NC := r.getD 8 0 },
    calls := Array.replicate (r.getD 1 0) default, kb := r.getD 9 0, m := r.getD 10 0,
    k := r.getD 11 0, mD := r.getD 12 0, kD := r.getD 13 0, mR := r.getD 14 0, kR := r.getD 15 0,
    filled := r.getD 16 0, fillD := r.getD 17 0, fillR := r.getD 18 0 }

theorem reads_standL (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 : Nat) :
    headReads (standL
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18]) =
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18] := by
  simp [headReads, standL]

/-- What is read of an owner, where all four things are there. -/
structure OwnerW where
  /-- the label of the stream that leaves the group -/
  label : Nat
  /-- rows and columns of the owner's last array that another sub-proof reads -/
  R : Nat
  K : Nat
  /-- what the owner's list records about it -/
  ec : Nat
  a : Nat
  p : Option ShP
  /-- the number of the owner's symbol arrays -/
  count : Nat
  /-- the owner's own entry for the stream -/
  entry : PlaceF
  deriving DecidableEq, Repr

/-- As ownerReads gives them. -/
def OwnerW.reads (w : OwnerW) :
    Option Nat × Option (Nat × Nat × Nat × Nat × Option ShP) × Nat × Except String PlaceF :=
  (some w.label, some (w.R, w.K, w.ec, w.a, w.p), w.count, .ok w.entry)

/-- An owner that holds these and nothing else. -/
def standO (w : OwnerW) : Owner :=
  { tl := { mats := #[{ name := "xbO", aId := w.label }], ix := { TX := #[0] },
            pkMat := Array.replicate (w.count - 1) 0, pxMat := #[0], plOwn := #[w.entry] },
    Fp := { trees := #[{ R := w.R, K := w.K }] },
    Tp := { nt := #[{ ec := w.ec, a := w.a, p := w.p }] }, iXO := 0 }

theorem reads_standO (w : OwnerW) (hc : 0 < w.count) (he : w.entry.whole = true) :
    ownerReads (standO w) = w.reads := by
  have e1 : (standO w).tl.ownEntry "stream" = .ok w.entry := by
    unfold HTailF2.ownEntry standO
    simp [he]
  unfold ownerReads OwnerW.reads
  rw [e1]
  simp [standO]
  omega

end AtFull.Head

#print axioms AtFull.Head.reads_standL
#print axioms AtFull.Head.reads_standO
