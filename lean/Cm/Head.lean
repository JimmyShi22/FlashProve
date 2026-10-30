-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/Head.lean: THE PLAIN HEAD: the conditions of the head's segment as the technical report
(lean/CREDITS.md) has them. Definitions only.

At each of the 1,024 positions the head has the conditions of the final normalisation (its ledger
of 99 bytes with 17 identities, the rounding of each of the 5,120 channels with its high digit, the
clamp); and at each position i and each token v of the vocabulary the plain margin
    mg_i[v] = ρ_i (lg_i[w_i] − lg_i[v] − [v < w_i]),      ρ_i = [r ≤ i < e],
w_i the token that position i checks, lg_i the logits that the cells of the normalisation's output
give with the output matrix, in three digits: K_2 in [0, 2^8), K_1 in [0, 2^16), and
mg − 2^8 K_1 − K_2 in 2^23 · [0, 2^16). So a margin is at least 0: at a covered position the checked
token has a greatest logit, and every smaller token a smaller one (proved for the head with the
scaled table, Cm/TargetPHead.lean, in Cm/TargetPHeadNoWrap.lean: `step_H6`, `noWrap`, under their
hypotheses). Where ρ_i = 0 all three digits are 0.

A key is a polynomial in the cells and the output matrix that must be an entry of a fixed table (a
lookup: `InLut`, Inst/Model/Head/Trace.lean); an identity is a polynomial in the cells that must be
0.

Main names:
  `mg`, `idn`: the plain margin; the 17 identities (those of Inst/Model/Head/TraceN.lean).
  `Fam`, `len`, `tableOf`: the seven families of keys, their lengths and tables (at HD0 the table of
    the third digit, R16; the relation's: `Plain.TP.tableOf`).
  `Small B`: every cell that the plain head reads, own or borrowed, is below B in absolute value.
  The field relation over these: `Plain.TP.RF`, Cm/TargetPHead.lean.

Why these widths: the text leaves the three widths open: m_2 ≤ m_0 ≤ m_2 + m_1, and the largest
margin 2 · 5,120 · 2,047 · 2^12 + 1 below 2^(m_0 + m_1). Here m_2 = 8, m_1 = 16, m_0 = 23, the
numbers of Inst/Model/Head/Trace.lean, which meet both; the digits overlap in one bit, so they are
not unique. By reading: "leaves the three widths open" is true of the report's appendix
on the model alone: its evaluation prints the three widths of its reference, and they are these.

Taken from Inst/Model/, unchanged: the type of the head's cells (`Head.Cells`: hf, hd, hr own, x
borrowed), the places of the arrays in them and the offsets of cells (`xv`, `nw`, `rn`, `d1`, `d2`,
`nrm`, `Dv`, `lg`, `K1`, `K2`), the ledger (Inst/Model/Common/Ledger.lean), the tables `R16`, `R8`,
`FC`.

Limits: no hidden number, no cost, no policy: that is the difference to the head's segment of
Inst/Model/Head/Trace.lean and Inst/Model/Head/TraceN.lean (its relation:
Policy/Rel/LedgerHead.lean), which is written after the programs and sends every covered position
below the last through a cost ledger. Gone are: ledger bytes 99 to 119,
the array ex with its two families of keys and its table, the term ρC (c + 2^37 b) of the margin,
and the four clauses on the hidden numbers. The arrays that remain fill an initial piece of each
matrix: features below 626,624 = 4 · 5,120 + 3 · 202,048 of hf (`nHf`), all 10,240 of hd, bytes
below 99 of hr (`nHr`).
Differences to the text, none of which moves the language (bookkeeping): the offsets of the digits'
cells are masked by ρ (K_1 = d1 + 32,896 ρ_i, K_2 = d2 + 128 ρ_i); offsets
and numbers of cells are those of Inst/Model/Head/.
A wart, declared: what the head reads of a request is the record `Head.Req`
(Inst/Model/Head/Index.lean), which has a field for a policy. No definition of this file reads that
field.
This file says nothing on the request's form; the identity "y = 0 if e < 1,024" is a condition on
the request alone and stands in Cm/TargetPRel.lean (`Cond.yZero`).
The conditions follow this protocol's technical report, which follows the texts named in
lean/CREDITS.md; the text is this library's.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Inst.Model.Head.TraceN

set_option autoImplicit false

namespace Cm.Plain

open Inst.Model Inst.Model.Head

/-- the families of keys -/
inductive Fam
  | NF | NFH | HD0 | HD1 | ROW | HD2 | CNF
  deriving DecidableEq, Repr

/-- the number of keys of a family at one position -/
def len : Fam → ℕ
  | .NF => 5120 | .NFH => 5120 | .HD0 => 202048 | .HD1 => 202048 | .ROW => 99
  | .HD2 => 202048 | .CNF => 5120

/-- the table of a family -/
def tableOf : Fam → Lut
  | .NF => R16 | .NFH => R16 | .HD0 => R16 | .HD1 => R16 | .ROW => R8 | .HD2 => R8 | .CNF => FC

/-- the features of hf and the bytes of hr that the plain head reads -/
def nHf : ℕ := 626624
def nHr : ℕ := 99

section Arrays
variable {K : Type} [CommRing K] (np : NormPar) (t : Cells K) (H : ℕ → ℕ → K) (y : Req)

/-- the plain margin -/
def mg (v i : ℕ) : K :=
  (y.rho i : K) * (Head.lg t H i (y.win i) - Head.lg t H i v - if v < y.win i then 1 else 0)

/-- The 17 identities at position i. -/
def idn (i k : ℕ) : K := Ledger.idn np (Ledger.Wsum nD fun l j => bl t l j i) (fun n => Dv t n i) k

end Arrays

/-- every cell that the plain head reads is below B in absolute value -/
def Small (B : ℤ) (t : Cells ℤ) : Prop :=
  ∀ i < nT,
    (∀ φ < nHf, |t.hf φ i| < B) ∧
    (∀ φ < nFeat .hd, |t.hd φ i| < B) ∧
    (∀ φ < nHr, |t.hr φ i| < B) ∧
    ∀ φ < nFeat .x, |t.x φ i| < B

end Cm.Plain
