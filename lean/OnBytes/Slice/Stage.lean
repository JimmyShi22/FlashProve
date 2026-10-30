-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Stage.lean: the claims between the blocks of the written proximity test (the joints),
in the library's relations.

The proximity test that ends a chain goes through stages. At a stage the verifier holds one linear
claim, a row, on the tables under one tree. A fold takes the claim to three folded rows. A code
switch takes it from there to the tables under the next tree. The base case ends the test. The
format's verifier holds a claim as arrays of words (Fmt/M1Types.lean: `GRow`, `SRow`) and reads
opened columns (`Col`). The library's blocks (Cb/Ld/LdSum.lean, LdSwitch.lean, LdBase.lean) speak of
a code whose words are read at the positions of a tree that may be longer than the code (the
library's "long positions"), a linear form, a target and a word. A mask code may be shorter than its
stage's tree. It is taken here as the code repeated to the tree's length (`ldRep`): each leaf of
the tree holds mask symbols of its own, and nothing makes two leaves agree.

This file fixes, once for all blocks, how the first is read as the second:
 the codes of a stage (`Sg.cIn`: main rows on the cube of h + g variables beside mask rows on the
 cube of the first h; `Sg.cFr`: the fresh mask rows; `Sg.cMid`: the three folded rows);
 a claim as a target and a vector of coefficients (`stmIn`, `stmMid`);
 the columns of a tree as words (`wordIn`, `wordFr`, `wordMid`);
 the relaxed relations (`Sg.RIn`, `Sg.RMid`): some message and tails have an encoding within e
 positions of the word, and the vector times the message is the target;
 what the decision reads of a written round (`rvOf`, `rsOf`).
Each block of the test is then one statement: if the claim before the block has no witness, the
prover has lost in the block's rounds and what follows, provided that it has lost in what follows
whenever the claim that the format's own function computes after the block has no witness.

Conventions. Entry (row b, place j) of a table with 2^k rows has the index (number of b) + 2^k * j.
The number of a vertex b has the digit b t at 2^t. A form is given as its vector of coefficients
(the library's `Slf.idf`).
No theorem is in this file.
-/
import OnBytes.Slice.CorePeel
import Cb.Ld.LdSum
import Fmt.M1Dec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- **A stage.** C: the code of a main row. Z: the code of a mask row. h + g: the number of row
variables, of which the mask rows have the first h. t: the number of positions drawn. -/
structure Sg where
  C : Fmt.M1.Code
  Z : Fmt.M1.Code
  h : ℕ
  g : ℕ
  t : ℕ

namespace Sg
variable (s : Sg)

/-- the stage in the format's record -/
def st : Fmt.M1.Stage := ⟨s.C, s.Z, s.h + s.g, s.h, s.t⟩

/-- the positions of the stage's tree -/
abbrev Ps : Type := Fin (2 ^ s.C.a)
/-- one main row, read at the tree's positions -/
abbrev cM : LdCode GE s.Ps := ldOf s.C s.C.a
/-- one mask row, under the mask code repeated to the tree's positions -/
abbrev cZ : LdCode GE s.Ps := ldRep s.Z s.C.a
/-- the tables before the fold: main rows beside the carried mask rows -/
abbrev cIn : LdCode GE s.Ps :=
  (s.cM.il (Fin (s.h + s.g) → Bool)).pair (s.cZ.il (Fin s.h → Bool))
/-- the fresh mask rows -/
abbrev cFr : LdCode GE s.Ps := s.cZ.il (Fin s.h → Bool)
/-- the three folded rows -/
abbrev cMid : LdCode GE s.Ps := s.cM.pair (s.cZ.pair s.cZ)

/-- **The relaxed relation before a fold**, at the radius e. -/
def RIn (e : ℕ) : (GE × (s.cIn.J → GE)) × s.cIn.Word → s.cIn.N.Wit → Prop :=
  ConL s.cIn.N e (Slf.idf (E := GE) (J := s.cIn.J)).Holds

/-- **The relaxed relation after a fold**, at the radius e. -/
def RMid (e : ℕ) : (GE × (s.cMid.J → GE)) × s.cMid.Word → s.cMid.N.Wit → Prop :=
  ConL s.cMid.N e (Slf.idf (E := GE) (J := s.cMid.J)).Holds

end Sg

/-- An entry of an array of words, in the field. -/
def vec (v : Array Fmt.M1.E) (i : ℕ) : GE := toE (Fmt.M1.ent v i)

/-- A list of words as a point. -/
def ptL (n : ℕ) (g : List Fmt.M1.E) : Fin n → GE := fun i => toE (g.getD i.val Fmt.Fld.zeroE)

section
variable (s : Sg)

/-- The coefficients of a row on a group. -/
def vecIn (G : Fmt.M1.GRow) : s.cIn.J → GE
  | .inl x => vec G.c (Sz.rowNo x.1 + 2 ^ (s.h + s.g) * x.2.val)
  | .inr x => vec G.d (Sz.rowNo x.1 + 2 ^ s.h * x.2.val)

/-- **A row on a group, as a statement.** -/
def stmIn (G : Fmt.M1.GRow) : GE × (s.cIn.J → GE) := (toE G.t, vecIn s G)

/-- The coefficients of what a fold hands on. -/
def vecMid (R : Fmt.M1.SRow) : s.cMid.J → GE
  | .inl j => vec R.c j.val
  | .inr (.inl j) => vec R.d0 j.val
  | .inr (.inr j) => vec R.d1 j.val

/-- **What a fold hands on, as a statement.** -/
def stmMid (R : Fmt.M1.SRow) : GE × (s.cMid.J → GE) := (toE R.t, vecMid s R)

/-- **The columns of a stage's tree as the word of main rows and carried mask rows.** Both kinds of
rows have a symbol at each position x of the tree, and it is taken from the column at x. -/
def wordIn (col : ℕ → Fmt.M1.Col) : s.cIn.Word := fun p =>
  match p with
  | .inl x => fun a => vec (col x.val).main (Sz.rowNo a.1)
  | .inr x => fun a => vec (col x.val).mask (Sz.rowNo a.1)

/-- The columns of a stage's tree as the word of the fresh mask rows. -/
def wordFr (col : ℕ → Fmt.M1.Col) : s.cFr.Word := fun x a => vec (col x.val).fresh (Sz.rowNo a.1)

/-- the first h coordinates of a point -/
def preP (γ : Fin (s.h + s.g) → GE) : Fin s.h → GE := fun i => γ (Fin.castAdd s.g i)

/-- **The three folded words**: the main rows at the point, both kinds of mask rows at its first h
coordinates. -/
def wordMid (col : ℕ → Fmt.M1.Col) (γ : Fin (s.h + s.g) → GE) : s.cMid.Word :=
  LdCode.mkW (SumPar.foldW s.cM γ (LdCode.fstW (wordIn s col)))
    (LdCode.mkW (C₁ := s.cZ) (C₂ := s.cZ)
      (SumPar.foldW s.cZ (preP s γ) (LdCode.sndW (wordIn s col)))
      (SumPar.foldW s.cZ (preP s γ) (wordFr s col)))

end

/-! ## What the decision reads of written rounds -/

/-- What the format's decision reads of a written round. -/
def rvOf (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal) : Fmt.M1.RV :=
  ⟨Fmt.M1.sentOf (PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2)),
    ((ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)).elems,
    ((ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)).poss⟩

/-- The same of a list of written rounds. -/
def rsOf : (ds : List PQ.RD) → Tr (PQ.uL (ckP .two) ds) → Fmt.M1.Rs
  | [], _ => []
  | d :: ds, (m, c, τ) => rvOf d m c :: rsOf ds τ

/-- The column at the position x of a written oracle; empty outside. -/
def colW (d : PQ.RD) (o : (wRound d).Orc) (x : ℕ) : List UInt64 :=
  if hx : x < PQ.posN d.tree then List.ofFn (o ⟨x, hx⟩) else []

end OnBytes.Slice
