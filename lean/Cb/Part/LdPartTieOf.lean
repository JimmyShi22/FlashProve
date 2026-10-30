-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartTieOf.lean: the ties at a closing (`LdPartTie`, Cb/Part/LdPartNext.lean) for the
concrete readings: the one reading of cells by a naming (`nm.out`, Cb/Part/LdPartCellsOut.lean) and
the front lookup's own clause on its bits (`L.ValidU`, Cb/Part/LdPartLkp.lean).

Definitions and one statement (`Cb.Spec.ldPartTieOf`); the proof is in
Cb/Part/LdPartTieOfProofs.lean. For arbitrary parameters: no closing and no body occurs; what is
used of them are maps of places and equations between entries.
A reading of messages here is an `LdPartOut` (Cb/Part/LdPartRide.lean): how the cells that have been
sent are read off the open messages: the matrices of cells, and two predicates on packing (exact,
relaxed); the reading R is an `LdPartRd` (Cb/Part/LdPart.lean). The ties are eight clauses between
the reading of the kept messages before, the reading of the open messages after, and the overwriting
of the further witness. In standard terms: consistency conditions between two consecutive parts of a
request: the cells that the part after a closing reads off its messages are, where these are a
packing (`O'.pkR m`), those that the kept messages and the overwritten further witness hold.

Why: the ties are a premise of `Spec.ldPartNext_step` (Cb/Part/LdPartNext.lean), on the model's step
at the head of segment k + 1; here they are stated to follow from `T.OK pp`, under the hypotheses of
`Spec.ldPartTieOf`.

Main names:
  `T : LdPartTieL P K k Sk S' St' J`: the record of parameters. p₀, nm₀, at₀: parameters, naming and
    places of the matrix of cells that the kept messages Sk hold; p₁, nm₁, at₁: those of the next
    body's matrix, among the messages S' open after the closing; kept, ov: the kept messages of a
    tuple after the closing; the further witness with the layer just sent overwritten; kR, kC: where
    a kept packed row and its columns are in the next body's matrix; oR, oC: where the packed rows
    of layer k + 1 and the Cw columns are; x', msg, R, e: the next front's reading of the instance
    off its states, of the entries J off the tuples, of entries as index matrix and cells, and the
    places of its lookup's names.
  `T.Ok`, `T.O'`, `T.L`, `T.vld`: the two readings `nm₀.out`, `nm₁.out`; segment k + 1's key
    functions at the reading R; vld st um := T.L.ValidU T.e st (T.msg um).
  `T.OK pp`: the conditions, all on numbers, namings, places and entries:
    numbers: the three packing factors are equal; radix, honest bound and window of p₀, p₁ are K's
      and P's; unique packing at the characteristic pp;
    namings: `nm₀.OK`, `nm₁.OK`; nm₀ is the part of nm₁ on kR, kC; segment k + 1's matrix is on oR,
      oC in the standard order; the two rectangles cover the next body's matrix; every row kept
      after k is named by nm₀, its matrix with the segment's number of columns;
    entries: the entry of a kept message at a place of nm₀'s matrix is the entry after the closing
      at the corresponding place of nm₁'s; ov touches layer k + 1 alone; layer k + 1 of the
      overwritten witness is what is at the own rectangle's places; its bits are what is at the
      places of the lookup's bit names;
    readings: the cells that R reads off the entries of a tuple are nm₁'s reading of the messages;
      the index matrix that R reads is the image of the matrix read off the index's message.
  `Spec.ldPartTieOf`: `P.Props p`, k + 1 < P.n, `T.OK pp` (pp the characteristic of E) (and whatever
    the arguments hold as proofs, among them `neC` of T's p₀, p₁ : `RngPar`: their types C of
    columns are not empty) ⇒ LdPartTie P K k T.Ok T.O' T.kept T.ov T.x' P.bitsV.ok T.vld.

Limits: where the conditions come from is not shown here: "entries" from the closing's places
and the lens of an addressing;
"readings" by the definition of the front's one type of entries.
This file gives no instance of `T.OK`, so as far as this file shows its theorems may hold of
nothing.
This file does not say that the reading of all open messages before a closing restricts to
`T.Ok` on the kept ones. It says nothing on masks.

Declared (by reading). "named" with "part": every row kept behind k stands in the next body's
matrix, also a row that only a later segment reads. In a write-up of ours (lean/CREDITS.md)
a segment's range predicate holds its own cells and the earlier matrices that this segment reads; a
matrix kept for a later one crosses it untouched. Here it enters the range check of every segment
that it crosses: more rows, more digits, a larger digits' lookup at each crossing. Why it is asked:
the clause rdKept of `LdPartTie` speaks of all rows kept behind k, and the virtual cells of a matrix
of packed entries (`cells`, Cb/Ld/LdRngAlg.lean) are 0 everywhere unless the whole matrix at hand is
a packing: a row can be read only as a part of the matrix at hand. A reading that unpacks unit by
unit would not need it.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Part.LdPartNext
import Cb.Part.LdPartCellsOut
import Cb.Part.LdPartTieNm
import Cb.Part.LdPartLkpBits
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Finset Cb.Rng Cb.RngPk IOR

/-- The record of parameters. -/
structure LdPartTieL {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] {Cf : LdCf F E} (P : LdPartD Cf) (K : LdPartPk) (k : ℕ) (Sk S' : Sig E)
    (St' J : Type) [Fintype J] where
  p₀   : RngPar
  p₁   : RngPar
  nm₀  : LdPartNm p₀
  nm₁  : LdPartNm p₁
  at₀  : p₀.Rp → p₀.C → Sk.Ent
  at₁  : p₁.Rp → p₁.C → S'.Ent
  kept : S'.Msg → Sk.Msg
  ov   : S'.Msg → LdPartW E → LdPartW E
  kR   : p₀.Rp → p₁.Rp
  kC   : p₀.C → p₁.C
  oR   : Fin (P.rp K (k + 1)) → p₁.Rp
  oC   : Fin K.Cw → p₁.C
  x'   : St' → Cf.Xm
  msg  : Cf.conf.Msg × S'.Msg → J → E
  R    : LdPartRd E J
  e    : ((P.keysOf (k + 1)).lk P.fmt.h (P.fmt.hi + P.fmt.lo) R x').Nm E → J

namespace LdPartTieL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  {Cf : LdCf F E} {P : LdPartD Cf} {K : LdPartPk} {k : ℕ} {Sk S' : Sig E} {St' J : Type}
  [Fintype J] (T : LdPartTieL P K k Sk S' St' J)

def Ok : LdPartOut E Sk := T.nm₀.out Sk T.at₀
def O' : LdPartOut E S' := T.nm₁.out S' T.at₁

/-- segment k + 1's key functions at the reading -/
def L : LdPartLk E St' J := (P.keysOf (k + 1)).lk P.fmt.h (P.fmt.hi + P.fmt.lo) T.R T.x'

/-- the lookup's own clause on its bits -/
def vld : St' → Cf.conf.Msg × S'.Msg → Prop := fun st um => T.L.ValidU T.e st (T.msg um)

/-- The conditions. -/
structure OK (pp : ℕ) : Prop where
  nP₀   : T.p₀.P = T.p₁.P
  nP    : K.P = T.p₁.P
  rdx₀  : T.p₀.rdx = K.rdx
  rdx₁  : T.p₁.rdx = K.rdx
  B₀    : T.p₀.B = P.B
  B₁    : T.p₁.B = P.B
  D₀    : T.p₀.D = P.D
  D₁    : T.p₁.D = P.D
  uniq  : Uniq (2 * P.D) K.rdx K.P pp
  ok₀   : T.nm₀.OK
  ok₁   : T.nm₁.OK
  part  : T.nm₀.PartOf T.nm₁ T.kR T.kC
  own   : T.nm₁.OwnAt K.P (k + 1) (2 ^ (P.seg (k + 1)).rowsLog) (P.seg (k + 1)).cols T.oR T.oC
  cover : ∀ i c, (∃ i' c', T.kR i' = i ∧ T.kC c' = c) ∨ ∃ i' c', T.oR i' = i ∧ T.oC c' = c
  named : ∀ q ∈ P.kept k, q.2 < T.nm₀.R q.1 ∧ T.nm₀.C q.1 = (P.seg q.1).cols
  keptE : ∀ m i c, Sk.ents (T.kept m) (T.at₀ i c) = S'.ents m (T.at₁ (T.kR i) (T.kC c))
  ovPk  : ∀ m w j, j ≠ k + 1 → (T.ov m w).pk j = w.pk j
  ovBit : ∀ m w j, j ≠ k + 1 → (T.ov m w).bit j = w.bit j
  ovOwn : ∀ m w i c, P.layW K (T.ov m w) (k + 1) i c = S'.ents m (T.at₁ (T.oR i) (T.oC c))
  ovB   : ∀ U m w (Y : Fin (2 ^ (P.keysOf (k + 1)).sz.dd)) (i : Fin (2 ^ (P.keysOf (k + 1)).sz.w)),
    T.msg (U, m) (T.e (.inl (Y, i))) = (T.ov m w).bit (k + 1) ((P.keysOf (k + 1)).sz.bitNo Y i)
  rdA   : ∀ U m, T.R.A (T.msg (U, m)) = T.O'.A m
  rdW   : ∀ U m, T.R.W (T.msg (U, m)) = fun y c => algebraMap F E (P.matU U y c)

end LdPartTieL

/-- The ties, for the concrete readings. -/
def Spec.ldPartTieOf : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Cf : LdCf F E)
      (P : LdPartD Cf) (K : LdPartPk) (p pp k : ℕ) [CharP E pp] (Sk S' : Sig E) (St' J : Type)
      [Fintype J] (T : LdPartTieL P K k Sk S' St' J),
    P.Props p → k + 1 < P.n → T.OK pp → LdPartTie P K k T.Ok T.O' T.kept T.ov T.x' P.bitsV.ok T.vld

end Cb
