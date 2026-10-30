-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/LinkAt.lean: the library's link protocol at the sizes and layouts of an entry file,
the decoder of a stored table, and the language of the link.

The library's link protocol (Cb/Ld/LdLink.lean) is stated for parameters: a code, a layout, a family
of oracle messages, radii, numbers of locations. This file gives each parameter the value that the
format's entry file has, from the record of sizes `Fmt.M3.Par` and four radii.

The values.
 Points and codes. The point of a position is the format's (`Fmt.M1.point`), read in the field. A
   word of a code (a, l, r) is the list of the values, at the 2^a points, of the polynomial whose
   coefficients are the r entries of the random tail and then the l entries of the message.
 A stored table. 2^v rows under the code T. A symbol as it is stored is a position with a list of
   words, meant to be 2^v of them. The table reads word number b of the list, 0 where the list is
   shorter, and does not read the position (the written verifier compares it, Run/PlanQX.lean:
   `symbolsCarryTheirPositions`). The row with the number b is the row at the vertex of the binary digits of b.
 The sample. The library lets a table come with a record (a seed and, for each row, answers of a
   sample of the row). Here the sample map is `Sample.nil`: one seed and no answer.
 The layout that is compared: all entries of a row's message before the cut, l - 3 s, where s is the
   format's number of a record's answers; at s = 0 these are all entries.
 The two folded rows. Each is one oracle message of R rows over the extension field under the code
   C. Entry e of a folded row stands in row e / l_C at place e % l_C. The message's entries stand
   from entry 0 on, the tail's from entry t0 on. The pad of the sample is the last place of the last
   row. The sample: the weights of a point on the cube, at the vertex of the binary digits of
   (row + 2^aR * place), and a factor other than 0 on the pad.

Main definitions: `Sz`, `ptOf`, `genOf`, `ldOf`, `ldRep`, `Sz.ix`, `Sz.memb`, `Sz.fam`, `Sz.lk`,
`Sz.seeds`, `Sz.dcd`, `Sz.Lang`.
Not claimed. No theorem is in this file but small facts on the definitions. That these values are
those of the programs is a matter of the files that carry a written protocol to this one.
-/
import Cb.Ld.LdLink
import Cb.Obj.LdObjectToyKit
import Cb.Ld.LdGroupStdMsg
import Fmt.M3Dec
import Run.PlanQX
import OnBytes.Slice.Draws
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood

/-- The point of a position of a code with 2^a positions, in the field. -/
def ptOf (a : ℕ) (x : Fin (2 ^ a)) : GF := toF (Fmt.M1.point a x.val)

/-- The generator matrix of a code: the coefficient number k of a word's polynomial (the tail's
entries first, then the message's) has the weight z^k at the position with the point z. -/
def genOf (C : Fmt.M1.Code) : Matrix (Fin (2 ^ C.a)) (Fin (C.r + C.l)) GE :=
  fun x k => algebraMap GF GE (ptOf C.a x ^ k.val)

/-- A position of a group with 2^a positions, as a position of the code C: modulo C's length. -/
def posIn (C : Fmt.M1.Code) {a : ℕ} (x : Fin (2 ^ a)) : Fin (2 ^ C.a) :=
  ⟨x.val % 2 ^ C.a, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- One row under the code C, read at the 2^a positions of a group. -/
@[reducible] def ldOf (C : Fmt.M1.Code) (a : ℕ) : LdCode GE (Fin (2 ^ a)) where
  NP := Fin (2 ^ C.a)
  NS := fun _ => Unit
  J := Fin C.l
  Q := Fin C.r
  enc := fun m r p _ =>
    (∑ q, genOf C p (Fin.castAdd C.l q) * r q) + ∑ j, genOf C p (Fin.natAdd C.r j) * m j
  Aa := Unit
  T := fun f x _ => f (posIn C x) ()
  src := fun x => {posIn C x}

/-- One row under the code C, repeated to the 2^a positions of a group. A word has a symbol at each
position of the group. The code word's symbol at the position x is C's own at x modulo C's length.
A word that is no code word may have different symbols at two positions that are equal modulo C's
length. This is not the library's `LdCode.rep` (Cb/Ld/LdRel.lean), whose words stand on C's own
positions and are read at x modulo C's length. -/
@[reducible] def ldRep (C : Fmt.M1.Code) (a : ℕ) : LdCode GE (Fin (2 ^ a)) where
  NP := Fin (2 ^ a)
  NS := fun _ => Unit
  J := Fin C.l
  Q := Fin C.r
  enc := fun m r p _ =>
    (∑ q, genOf C (posIn C p) (Fin.castAdd C.l q) * r q) +
      ∑ j, genOf C (posIn C p) (Fin.natAdd C.r j) * m j
  Aa := Unit
  T := fun f x _ => f x ()
  src := fun x => {x}

/-- **The sizes**: the format's record, four radii (counts of positions), and what the definitions
below need of the sizes. eM: the radius at which a stored table is decoded. e0, e1: the radii at
which the two folds are tested. eU: the radius of a folded row's oracle message. -/
structure Sz where
  P : Fmt.M3.Par
  eM : ℕ
  e0 : ℕ
  e1 : ℕ
  eU : ℕ
  hR : 0 < P.R
  hl : 0 < P.C.l
  fitM : P.T.l ≤ P.R * P.C.l
  fitT : P.t0 + P.T.r ≤ P.R * P.C.l

namespace Sz
variable (S : Sz)

/-- positions of a stored table; coefficients of a row's polynomial; entries of a row's message -/
abbrev Pos : Type := Fin (2 ^ S.P.T.a)
/-- See `Pos`. -/
abbrev Co : Type := Fin (S.P.T.r + S.P.T.l)
/-- See `Pos`. -/
abbrev En : Type := Fin S.P.T.l
/-- the entries that are compared -/
abbrev Lay : Type := Fin S.P.cut

/-- **The format of a stored table.** -/
@[reducible] def ix : LdIx GE S.Pos S.Co S.En where
  v := S.P.v
  G := genOf S.P.T
  pl := fun j => Fin.natAdd S.P.T.r j
  Z := Sample.nil GE S.En
  eM := S.eM
  rank := fun M => (Fintype.equivFin _ M).val

/-- the number of a row: the vertex's digits, the lowest first -/
def rowNo {v : ℕ} (r : Fin v → Bool) : ℕ := ∑ t, if r t then 2 ^ t.val else 0

/-- **The link on vectors.** -/
@[reducible] def lw : LdLkW GE S.Pos S.Co S.En S.Lay where
  X := S.ix
  lay := fun a => ⟨a.val, lt_of_lt_of_le a.isLt (Nat.sub_le _ _)⟩
  l := S.P.aPhi
  pl := fun a t => a.val.testBit t.val

/-- the entries of a folded row's oracle message: (row, place), and no mask row -/
abbrev MJ : Type := (Fin S.P.R × Fin S.P.C.l) ⊕ (Empty × Fin S.P.Z.l)

/-- the pad's place: the last place of the last row -/
def padJ : S.MJ :=
  .inl (⟨S.P.R - 1, Nat.sub_lt S.hR Nat.one_pos⟩, ⟨S.P.C.l - 1, Nat.sub_lt S.hl Nat.one_pos⟩)

/-- the index of an entry in the member's table -/
def idxJ : S.MJ → ℕ
  | .inl x => x.1.val + 2 ^ S.P.aR * x.2.val
  | .inr x => x.1.elim

/-- **A folded row's oracle message.** -/
@[reducible] def memb : StdM GE (Fin (2 ^ S.P.C.a)) where
  Cm := ((ldOf S.P.C S.P.C.a).il (Fin S.P.R)).pair ((ldOf S.P.Z S.P.C.a).il Empty)
  Dt := {j : S.MJ // j ≠ S.padJ}
  place := (splitAt S.padJ).symm
  μ := Fin (S.P.aR + S.P.aP)
  plc := fun j t => (S.idxJ j.1).testBit t.val
  B := GEˣ
  b := Units.val
  e := S.eU

/-- **The family that is sent in one message**: the first table's folded row (false), the copy's
(true). -/
@[reducible] def fam : Sig GE := { O := Bool, om := fun _ => S.memb.om }

/-- the entry of a folded row at which a coefficient of the fold's polynomial stands -/
def entryOf (k : S.Co) : ℕ := if k.val < S.P.T.r then S.P.t0 + k.val else k.val - S.P.T.r

theorem entryOf_lt (k : S.Co) : S.entryOf k < S.P.C.l * S.P.R := by
  have h1 := S.fitM
  have h2 := S.fitT
  have h3 := k.isLt
  rw [Nat.mul_comm]
  unfold entryOf
  split <;> omega

/-- where a coefficient of the fold's polynomial stands in the oracle message -/
def putAt (k : S.Co) : S.MJ :=
  .inl (⟨S.entryOf k / S.P.C.l, Nat.div_lt_of_lt_mul (S.entryOf_lt k)⟩,
    ⟨S.entryOf k % S.P.C.l, Nat.mod_lt _ S.hl⟩)

/-- **The library's link at these sizes.** A symbol of a stored table is a position with a list of
words. A missing word is read as 0. The position is not read. -/
@[reducible] def lk : LdLkP GE S.Pos S.Co S.En S.Lay where
  D := S.lw
  Sy := Run.PQ.SgX
  up := fun s r => algebraMap GF GE (toF (s.2.getD (rowNo r) 0))
  e₀ := S.e0
  e₁ := S.e1
  t₀ := S.P.nu0
  t₁ := S.P.nuj
  N := S.fam
  i₀ := false
  l₀ := S.putAt
  i₁ := true
  l₁ := S.putAt

/-- **The seeds**: one point and one factor for both members. -/
@[reducible] def seeds : S.fam.Seeds where
  D := (Fin (S.P.aR + S.P.aP) → GE) × GEˣ
  sd := fun _ s => s
  mult := fun _ => 1

/-- the one value of `ix.Rec`: the sample map of `ix` is `Sample.nil` -/
def rec0 : S.ix.Rec := ((), fun x => x.2.elim)

/-- **The decoder of a stored table**: the message parts of the nearest table of code words, if one
is within eM columns. Below half the code's distance there is at most one. Beyond it ties are broken
by a fixed order (`ix.rank`). -/
def dcd (f : S.Pos → Run.PQ.SgX) : Option (S.ix.Row × S.En → GE) :=
  S.ix.dec (S.lk.tab f) S.rec0

/-- **The language of the link**: the first table does not decode, or the copy decodes to the same
rows' messages. The first clause is a way out: OnBytes/Slice/README.md, "The way out and the key".
-/
def Lang (y : (S.Pos → Run.PQ.SgX) × (S.Pos → Run.PQ.SgX)) : Prop :=
  S.dcd y.1 = none ∨ S.dcd y.2 = S.dcd y.1

end Sz
end OnBytes.Slice

#print axioms OnBytes.Slice.Sz.entryOf_lt
