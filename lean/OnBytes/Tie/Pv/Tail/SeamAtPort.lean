-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/SeamAtPort.lean: the seam between the smallness test's round and the lookup on
its digits (Cb/Pv/Tail/SeamD.lean), at the verifier's own record of a smallness test.

SeamD.lean has the seam at letters: a record `Late` with the late messages, the entries, a numbering
of the lookup's keys and a map `ix` from the test's digits to the numbering's. Here that record is
filled at tl : OnBytes.Model.HTailF2: the sizes are `sizeOf tl` (SizeOf.lean); the numbering is
`portQJ tl en` (OnBytes/Tie/Pv/Lookup/Digits/PortJ.lean); `ix` is `ixP` (PortCols.lean); the further
witness in front of the sending is the digits read off the messages, beside the witness behind.

Main names:
  `Caller K tl`: what stays a letter: the explicit statement, the early and the late messages, the
    implicit instance, the further witness behind the sending; the weights, the symbols and the
    vector of reads; what else the joint says; the caller's type of entries J, how the messages are
    read as entries (`ent`), and how J names the entry (array, row, column) (`en`).
  `Caller.theta`, `Caller.letters`: the letters of the typed smallness test at `sizeOf tl`; the
    further witness is (the digits, the witness behind).
  `ixAt`: the digit (matrix, combination, row of cells) as a place of the lookup.
  `Caller.late`: the record `Late`. `late_reads`: its law `Reads`, by rfl. `late_ok`: the laws of
    its numbering at the two tables' sizes, under `shapeTest2`.
  `late_zl`, `late_zh`: the digits that it reads are the entries of ZZ in row u and in the columns
    that the verifier's `zzCol` gives for (mu, plane 0 or 1, i).
  `seam_port`: under `shapeTest2 tl pp` and `colsTest tl`: the relaxed relation from which the
    lookup on the digits starts, at an early and a late tuple of messages, gives the relaxed
    relation at which the round ends, at the early tuple.
Limits: `shapeTest2` and `colsTest` are Bools on public numbers: that they are true at a given
sub-proof is a run, no proof term. `ent` and `en` are letters: that the entries which `ent` reads
under `en` are what the prover commits to in ZZ is not said. `sym`, `u3` and `phi` are letters
beside `ent` and `en`: nothing ties the symbols and the reads, which stand in the same equations as
the digits, to entries of committed arrays, nor `phi` to the record's tables. The moment of the
record matters for the tables of reads (SizeOf.lean, Limits). No lookup occurs, and no sending: the
join of the three blocks is not here. Nothing on an honest prover.

-/
import Cb.Pv.Tail.SeamD
import OnBytes.Tie.Pv.Tail.SizeOf
import OnBytes.Tie.Pv.Lookup.Digits.PortSeam
import OnBytes.Tie.Pv.Lookup.Digits.PortCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.DgP Cb.Pv.Tail Iop CbQ

/-- What stays a letter at the verifier's record. -/
structure Caller (K : Type) (tl : HTailF2) where
  /-- the explicit statement, the early messages, the implicit instance -/
  X : Type
  M : Type
  E : ExtSpec
  /-- the late messages; the further witness behind the sending; the entries' names -/
  U : Type
  W₀ : Type
  J : Type
  /-- the weights of a table, the committed symbols, the committed vector of reads -/
  phi : X → ℕ → ℕ → K
  sym : M → ℕ → ℕ → ℕ → K
  u3 : M → ℕ → K
  /-- what else the joint says -/
  ride : X × E.Str → M → Dig K (sizeOf tl).size × W₀ → Prop
  /-- the entries of an early and a late tuple of messages -/
  ent : M × U → J → K
  /-- how J names the entry (array, row, column) -/
  en : Ent3 → J

variable {K : Type} {tl : HTailF2}

/-- The letters of the typed smallness test, at plain numbers. -/
def Caller.theta (C : Caller K tl) : TLetters K (sizeOf tl) where
  X := C.X
  M := C.M
  E := C.E
  W := Dig K (sizeOf tl).size × C.W₀
  phi := C.phi
  sym := C.sym
  u3 := C.u3
  dig := Prod.fst
  ride := C.ride

/-- The digit (matrix, combination, row of cells) as a place of the lookup on the digits. -/
def ixAt (h : colsTest tl = true) (x : DIx (sizeOf tl).size) : Pl tl :=
  ixP h x.1.val x.2.2.val x.2.1.val x.1.isLt x.2.2.isLt x.2.1.isLt

section
variable [Field K]

/-- The letters of Cb/Pv/Tail/Block.lean. -/
def Caller.letters (C : Caller K tl) : Letters K (sizeOf tl).size := C.theta.letters

/-- The digits, read off the messages at their places in ZZ. -/
def Caller.digs (C : Caller K tl) (h : colsTest tl = true) (m : C.M × C.U) :
    Dig K (sizeOf tl).size :=
  ⟨fun μ u i => C.ent m ((portQJ tl C.en).lo (ixAt h ⟨μ, u, i⟩)),
    fun μ u i => C.ent m ((portQJ tl C.en).hi (ixAt h ⟨μ, u, i⟩))⟩

/-- The record of the seam, at the verifier's record. -/
def Caller.late (C : Caller K tl) (h : colsTest tl = true) : Late C.letters where
  U := C.U
  W₀ := C.W₀
  I := Pl tl
  J := C.J
  bk := fun m w => (C.digs h m, w)
  ent := C.ent
  ix := ixAt h
  Q := portQJ tl C.en

/-- The witness that `bk` makes holds the digits of the messages. -/
theorem late_reads (C : Caller K tl) (h : colsTest tl = true) : (C.late h).Reads :=
  fun _ _ => rfl

/-- The laws of the numbering, at the sizes of the two tables. -/
theorem late_ok (C : Caller K tl) (h : colsTest tl = true) {pp : ℕ}
    (hs : shapeTest2 tl pp = true) :
    (C.late h).Q.DatOK (sizeOf tl).size.lo (sizeOf tl).size.hi pp :=
  dgP_port_okJ C.en (shape2_parts hs).1

/-- The low digits that are read are the entries of ZZ in the verifier's own columns. -/
theorem late_zl (C : Caller K tl) (h : colsTest tl = true) (m : C.M × C.U)
    (μ : Fin (sizeOf tl).size.NM) (u : Fin (sizeOf tl).size.tau)
    (i : Fin ((sizeOf tl).size.m μ)) :
    ∃ col, tl.zzCol μ.val 0 i.val = some col ∧
      ((C.late h).digs m).zl μ u i = C.ent m (C.en (tl.ix.ZZ, u.val, col)) :=
  ⟨_, (dgP_ix_lo h μ.isLt i.isLt u.isLt).1, rfl⟩

/-- The same for the high digits. -/
theorem late_zh (C : Caller K tl) (h : colsTest tl = true) (m : C.M × C.U)
    (μ : Fin (sizeOf tl).size.NM) (u : Fin (sizeOf tl).size.tau)
    (i : Fin ((sizeOf tl).size.m μ)) :
    ∃ col, tl.zzCol μ.val 1 i.val = some col ∧
      ((C.late h).digs m).zh μ u i = C.ent m (C.en (tl.ix.ZZ, u.val, col)) :=
  ⟨_, (dgP_ix_hi h μ.isLt i.isLt u.isLt).1, rfl⟩

/-- The seam, at the verifier's own record. -/
theorem seam_port (C : Caller K tl) (h : colsTest tl = true) {pp : ℕ}
    (hs : shapeTest2 tl pp = true) :
    ∀ b m u w, (C.late h).inD.relR b ((m, u), w) →
      (B C.letters).relR b (m, (C.late h).bk (m, u) w) :=
  seam (C.late h) (late_ok C h hs) (late_reads C h)

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.late_reads
#print axioms OnBytes.Tie.Pv.Tail.late_ok
#print axioms OnBytes.Tie.Pv.Tail.late_zl
#print axioms OnBytes.Tie.Pv.Tail.late_zh
#print axioms OnBytes.Tie.Pv.Tail.seam_port
