-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetPRel.lean: the relation pair of the integer model at a variable prime p: the conditions
are formed modulo p, and no condition has a prime inside (for the head by its definitions
(Cm/TargetPHead.lean; `Plain.idn`: Cm/Head.lean); for the 24 segments of the layers by a reading of
Inst/Model, of which the proofs of `forces` and `admits` for every prime p with 2^61 - 1 ≤ p and
every lawful table are the check).

This file defines an indexed relation in two forms, strict (`Ryes`) and relaxed (`Rno`: a larger
bound on the witness's cells that some segment reads: `Below2`). An index is a well-formed digit
matrix (`Idx`), an instance a request (1,024 tokens, the two numbers r, e of the covered range, the
announced token y), a witness integers at the names of cells (`Trace`); the forward pass's own
cells are the honest trace (`trace2 s`).
Definitions and statements (`Cm.TP.Spec.forces` and the like); the proofs are in
Cm/TargetPRelProofs.lean.
Why: a request's preamble over a field F shows conditions modulo the characteristic of F. The
theorems that are stated at `Cb.Gl.F`, `Cb.Gl.E` (Cb/Gl/GlField.lean) stand over
p = 2^64 - 2^32 + 1. So the pair is stated with the prime as a parameter.
What is taken from Cm/Rel2.lean, Cm/RelBase.lean: indices
(well-formed digit matrices: `Idx`), requests (`Instance ppref`), cells (`Trace`), tables of scales
with `Scales.Lawful`, the bound on cells (`Below2`), what the head reads of a request (`reqOf`),
the honest trace (`trace2 s`), and what a true request is (`TrueAt`).

Main names:
  `castW p`, `castH p`, `segFF p`: the index matrix, the output matrix, and keys, tables and
    identities of a feed-forward segment, in the integers modulo p.
  `CondL p κ nf W tok T`: the conditions of the 24 segments of the layers at the words κ, modulo p.
    No bound on a cell is among them. (nf, the final normalisation, is an argument of the table of a
    segment (`Scl`, Inst/Model/Scl.lean); no key or identity of a layer reads it.)
  `Cond p s W x T`: all conditions: those of the layers; the plain head with the scaled table
    (Cm/TargetPHead.lean: the third digit of a margin lies in 2^23 · [0, 2^16): no inverse);
    y = 0 if e < 1,024.
  `Ryes p s i x T`: r < e ∧ `Below2 129 T` ∧ `Cond p s i.mat x T`.
  `Rno p s i x T`: r < e ∧ `Below2 (2 ^ 18) T` ∧ `Cond p s i.mat x T`.
Stated for every prime p with 2^61 - 1 ≤ p and every lawful table s, with no other hypothesis on p
and s:
  `Spec.sub`: every witness in `Ryes` is one in `Rno` (every p, every table).
  `Spec.admits`: if a request has a witness in `Ryes`, the honest trace is one. (This is the clause
    "admits" of a configuration. What a write-up of ours (lean/CREDITS.md) calls "the
    conditions admit the reply", a true request has cells below the strict bound, is `trace_iff` and
    `lang_yes` from
    right to left.)
  `Spec.forces`: every witness in `Rno` shows that the request is true: nothing wraps around.
  `Spec.lang_yes`, `Spec.lang_no`: x has a witness in `Ryes` ⇔ x has a witness in `Rno` ⇔ `TrueAt`
    at the table's scales (`s.kap`, `s.nf`).
  `Spec.trace_iff`: the honest trace is a witness in `Ryes` exactly of the true requests.
  `Spec.lang_main`: to have a witness in `Rno` is the relation "exact match" of
    Inst/Model/ProgramR.lean (`RinfS`) at the index that the matrix holds.

The statements do not range over nothing. A prime: p = 2^64 - 2^32 + 1 (Cb/Gl/GlField.lean:
`Cb.Gl.gl_prime`). A lawful table: Cm/Rel2Guards.lean: `lawful_sRef`. The facts on true requests of
Cm/RelTrue.lean give "has a witness" here, at lawful tables, by `Spec.lang_yes`, `Spec.lang_no`
(four of them, one by `Spec.trace_iff`, and `lawful_sRef`, in the letters of a configuration:
Cm/TargetPLangs.lean).

Limits: the size condition 2^61 - 1 ≤ p is the bound at which the proofs of Inst/Model stand: every
quantity that they compare with the prime is below 2^61 - 1. It takes the place of the
write-up's last size condition (the largest side of a condition lies below the prime), with a
rider: there the bound is the configuration's own maximum; here it is one threshold for all lawful
tables: the same kind of condition, narrower (a prime between a table's true maximum and 2^61 - 1
is shut out), and `Scales.Lawful` bears the burden of keeping every side below 2^61 - 1. The other
size conditions are `Scales.Lawful`.
This file says nothing below 2^61 - 1, but for the definitions and `Spec.sub`, which stand at every
p. It does not say that this list of conditions is the write-up's: it is the copied
library's list with the head's third key written as in the write-up. Held against the
write-up, by reading: the head: its 17 identities and its three margin keys with the widths
(8,
16, 23) are the write-up's at its reference, one for one; the digit keys of a normalisation
lie in another table (width 8 with a public multiplier; there width 16).

All 25 pieces were held against a print of the write-up, condition by condition, once, by reading
(both ways; definitions and statements, no proof; nothing compiled; not machine-checked): no
condition of it on a cell that some segment reads was found missing at a table that both admit; Lean
asks less in one place, of a witness alone: the bound on cells is not asked of names that no segment
reads (declared: the head of Cm/Rel2.lean); no row says that a request could be true here and false
there at such a table. The integer program is
its program, step for step; the scales, sizes and constants of the model that it prints for its
reference are Lean's, digit for digit; its counts of cells and keys of a segment are not: (b), (c),
(g). Which tables are admitted differs, as the head of Cm/Rel2.lean declares (wider below 16 and in
the gap shift, narrower above).
Differences of form that no other head declares:
  (a) digits of at most 8 bits lie in a range table of 2^8 rows with a public multiplier, not only
      in the head: ten families of keys of a feed-forward segment, among them the remainder digits
      of attention's value and output products, and the 99 digits of every normalisation; the
      write-up fills them up to its one width; the ranges forced are the same; a segment has
      one table more;
  (b) a rounding's remainder digit is kept, cell and key, at shift 16, where the key forces 0 and
      the write-up has no digit: at the reference: the two gates;
  (c) the sigmoid's value stands in three cells and attention's denominator in four: one more than
      the write-up's rule gives;
  (d) in a normalisation one number has its short digit lowest;
  (e) the cells of an attention segment's empty tile slots stand under two keys, where the
      write-up leaves them idle: here Lean asks more, of cells that no sum reads and that the
      honest trace fills;
  (f) off the gap shift 8 the gap digit's table and the step of its dead rows are no instance of
      the write-up's type (at 8: the same, digit for digit);
  (g) the head's large matrix is about twice as wide as the plain head needs;
  (h) the form of a segment's maps and matrices, the protocol's side: a channel is a plain number
      here and a padded triple there, so that Lean's placement does not meet the write-up's
      hypothesis on placements to the letter; one index atom a layer; one family for what are
      separate key maps there; the router's families over all four layers; no joint key map a
      table; degrees counted as atoms, 13 paid for 12.
And: the pointers in the comments of Inst/Model/ (definitions, tables, step names) go to another
text's labels: none of them exists in that print (by a reading).
The list is that reading's, not shown complete.
None moves this relation's language: here, for a prime p with 2^61 - 1 ≤ p and a lawful table, "has
a witness" is "true of the program" by a theorem, whatever the form of cells and keys (`lang_no`,
`trace_iff`); that the write-up's own conditions have its program's language is the
write-up's theorem, not Lean's. What the write-up does not print and this library fixes can
be held against nothing: the entries of the five table functions, the placement of the weights in
the index, some bases, shifts and numbers of digits. Not reached by that reading: proofs; which
maps a sumcheck reveals; the counts of a segment's variables and rounds.
What the heads of Cm/Rel2.lean and Cm/RelBase.lean list as not said is not said here either (a
lawful table need not be sensible; no weights are in sight; names of cells that no segment reads
are free). This file says nothing on segments as polynomial maps, and nothing on protocols.
At p = 2^64 - 2^32 + 1 the model's segments are `Cm.Seg.TS.segM s k` (Cm/TargetSegModel.lean).
`Cm.Seg.TS.Spec.model_equiv`, stated there and proved in Cm/TargetSegModelProofs.lean: for every
table s, every request x, every integer index matrix W and all integer matrices M of cells,
`Cond Cb.Gl.p s W x` holds at the trace of M if and only if the conditions of all 25 segments hold
at (x, W, M).
Terms: lean/GLOSSARY.md.
The notions follow the worked example named in lean/CREDITS.md; the text is this library's.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
"The copied library" in this file's comments: folders of this library itself, such as Blocks/, Iop/
and Inst/ (lean/CREDITS.md).
-/
import Cm.Rel2
import Cm.TargetPHead

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.TP

open Inst.Model Inst.Model.All
open Inst.Model.Layout (kRef hRef)

variable (p : ℕ)

/-- the matrix, entry by entry modulo p -/
abbrev castW (W : Mat) : ℕ → ℕ → ZMod p := fun r c => ((W r c : ℤ) : ZMod p)

/-- the output matrix that the layout reads from W, entry by entry modulo p -/
abbrev castH (W : Mat) : ℕ → ℕ → ZMod p := fun j v =>
  (((Layout.weightsOf ppref kRef W).H j v : ℤ) : ZMod p)

/-- Keys, tables and identities of the feed-forward segment of group g at the layers' scales κ,
modulo p. -/
abbrev segFF (κ : ℕ → LayerScale) (nf : NormPar) (g : ℕ) : Blocks.TraceSpec (ZMod p) (ℕ → ℕ) :=
  FFSeg.trace (scl := SFK κ nf g) FFSeg.Dim.ref tbRef kRef (4 * g) (decide (g = 0)) (ZMod p)

/-- The conditions of the 24 segments of the layers, formed modulo p: every key is an entry of its
table and every identity is 0. -/
structure CondL (κ : ℕ → LayerScale) (nf : NormPar) (W : Mat) (tok : ℕ → ℕ) (T : Trace) : Prop where
  ffKey : ∀ g < nGr,
    ∀ k, (segFF p κ nf g).key tok (castW p W) (fun c => T.vFF g c.val) k ∈ (segFF p κ nf g).table k
  ffIdn : ∀ g < nGr, ∀ j, (segFF p κ nf g).idn tok (castW p W) (fun c => T.vFF g c.val) j = 0
  attKey : ∀ g < nGr, ∀ (c : Fin 4) (X : ℕ), X < (DAK κ g).used c →
    AttSeg.keyVec (scl := SFK κ nf g) (DAK κ g) tbRef
        (AttSeg.castT (T.vAtt g) : AttSeg.Raw → ZMod p) c X ∈
      AttSeg.lutSet (AttSeg.lut (scl := SFK κ nf g) (DAK κ g) tbRef c)
  attIdn : ∀ g < nGr, ∀ j : AttSeg.Idn, j.Valid (DAK κ g) →
    AttSeg.idnVal (DAK κ g) (AttSeg.castT (T.vAtt g) : AttSeg.Raw → ZMod p) j = 0

/-- The conditions, formed modulo p: in each of the 25 segments every key is an entry of its table
and every identity is 0; and y = 0 if e < `ppref.T`. -/
structure Cond (s : Scales) (W : Mat) (x : Instance ppref) (T : Trace) :
    Prop extends CondL p s.kap s.nf W (tokOf x.prompt) T where
  headKey : ∀ f a i, a < Plain.len f → i < Head.nT →
    Head.InLut (Plain.TP.tableOf f)
      (Plain.TP.key s.nf (T.vHead.cast (ZMod p)) (castH p W) (reqOf x) f a i)
  headIdn : ∀ i < Head.nT, ∀ k < 17, Plain.idn s.nf (T.vHead.cast (ZMod p)) i k = 0
  yZero : x.e < ppref.T → ((x.y.val : ℕ) : ZMod p) = 0

/-- The relation: r < e, every cell that some segment reads below 129 in absolute value (`Below2`),
the conditions modulo p. -/
def Ryes (s : Scales) (i : Idx) (x : Instance ppref) (T : Trace) : Prop :=
  x.r < x.e ∧ Below2 129 T ∧ Cond p s i.mat x T

/-- Its relaxation: the same with the bound 2^18. -/
def Rno (s : Scales) (i : Idx) (x : Instance ppref) (T : Trace) : Prop :=
  x.r < x.e ∧ Below2 (2 ^ 18) T ∧ Cond p s i.mat x T

namespace Spec

/-- Ryes ⊆ Rno -/
def sub : Prop :=
  ∀ (p : ℕ) (s : Scales) (i : Idx) (x : Instance ppref) (T : Trace), Ryes p s i x T → Rno p s i x T

/-- For a prime p with 2^61 - 1 ≤ p and a lawful table s: if there is a witness, the honest trace
is one. -/
def admits : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ s : Scales, s.Lawful →
      ∀ (i : Idx) (x : Instance ppref) (T : Trace), Ryes p s i x T → Ryes p s i x (trace2 s i x)

/-- For a prime p with 2^61 - 1 ≤ p and a lawful table s: every witness of the relaxation shows
that the request is true. -/
def forces : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ s : Scales,
      s.Lawful → ∀ (i : Idx) (x : Instance ppref) (T : Trace), Rno p s i x T → TrueAt s.kap s.nf i x

/-- For a prime p with 2^61 - 1 ≤ p and a lawful table s (with `lang_no` below): the two languages
are one: the true requests. -/
def lang_yes : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ s : Scales,
      s.Lawful → ∀ (i : Idx) (x : Instance ppref), (∃ T, Ryes p s i x T) ↔ TrueAt s.kap s.nf i x
def lang_no : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ s : Scales,
      s.Lawful → ∀ (i : Idx) (x : Instance ppref), (∃ T, Rno p s i x T) ↔ TrueAt s.kap s.nf i x

/-- For a prime p with 2^61 - 1 ≤ p and a lawful table s: to have a witness in `Rno` is the relation
"exact match" of Inst/Model/ProgramR.lean (`RinfS`) at the index that the matrix holds. -/
def lang_main : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ s : Scales, s.Lawful →
      ∀ (i : Idx) (x : Instance ppref),
        (∃ T, Rno p s i x T) ↔ RinfS ppref s.kap s.nf (fun _ => tbRef) i.index x

/-- For a prime p with 2^61 - 1 ≤ p and a lawful table s: the honest trace is a witness exactly of
the true requests. -/
def trace_iff : Prop :=
  ∀ p : ℕ, p.Prime → 2 ^ 61 - 1 ≤ p →
    ∀ s : Scales, s.Lawful →
      ∀ (i : Idx) (x : Instance ppref), Ryes p s i x (trace2 s i x) ↔ TrueAt s.kap s.nf i x

end Spec

end Cm.TP
