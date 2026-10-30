-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/Rel2.lean: the model with the plain head, the cells as witness: tables of scales without a
policy, the bound on cells, the honest trace.

In standard terms: parts of an indexed relation for the model: the index is the digit matrix of the
weights, the instance a request, the witness the cells. The relation, at a prime p, is
Cm/TargetPRel.lean; it takes these parts from here.

Definitions; lemmas on them are in Cm/Rel2Proofs.lean.

Index (a well-formed digit matrix), requests, cells and the bound on the cells of the 24 segments of
the layers are those of Cm/RelBase.lean. The head's conditions are those of Cm/TargetPHead.lean
(keys, tables) and Cm/Head.lean (the margin, the identities): the final normalisation, and at every
position and token the plain margin in three digits. For a table s of scales (a parameter of
everything below, no part of an index):
  `Scales`, `Scales.kap`, `Scales.Lawful`: No policy. "Lawful" is written out: equations and
    inequalities between numbers of the table alone.
  `Below2 B T`: the bound; the head's cells under it: features below 626,624 of hf, all 10,240 of
    hd, bytes below 99 of hr.
  `trace2 s i x`: the honest trace, a named function of index and request: the cells that the rules
    of the layers' segments write (Cm/Rel2LayersHon.lean) and the honest cells of the plain head
    (Cm/HeadHonest.lean).
  (`TrueAt`, Cm/RelBase.lean): a true request, written out there; among its clauses: the integer
    program at the table runs on the 1,024 tokens with the weights of the matrix (no range test
    fails at any position, covered or not); at every covered position the checked token is the
    model's first choice.
A wider family than the text's. The text has one shift of the attention gap for all layers; a
lawful table has one value in each group of four layers, free from group to group (4 to 12). So
"for every lawful table" ranges over more integer programs than the text defines. Nothing is
restricted for it. In the other direction "lawful" asks more than the text's size conditions at
some places (K ≤ M, 24 ≤ M, upper ends of shifts) and less at others (shifts below 16).
Differences of `Cm.TP.Cond` (Cm/TargetPRel.lean) to the text's list of conditions, none of which
moves the language: offsets and numbers of cells; one joint key for two digits of a division in
attention; no ordered list and no single bound on the largest value: that nothing wraps around is
shown key by key.

Limits: this file does not say that a table is sensible. "Lawful" asks K ≤ M of all 97
normalisations and 24 ≤ M; that shuts out tables at which a normalisation puts out 0 whatever its
input (for instance exponent 10 with shift 16, which size conditions without a lower end on the
exponent admit), where, if it is the final one, token 0 is the first choice everywhere whatever the
weights. It does not shut out every idle table: the library from which the model's files are copied
exhibits lawful scales at which none of the 48 layers adds anything to the stream whatever its
weights (in a file that is not copied here). At such a table a statement over every lawful table
says little of the weights.
Two lawful tables at which such a statement says little of the weights: Cm/Rel2Idle.lean (what is a
theorem there and what is by hand: the top of that file).
This file says nothing on codes, oracles or protocols.
It says nothing on segments as polynomial maps. It says nothing on any fitted table or
real weights. That "the integer program" is the model that the text describes is a comparison by
reading of two definitions, and no theorem. The type `All.Trace` has names that no segment reads;
no relation on the cells says anything of the values there.
The notions and the head's conditions follow the worked example named in lean/CREDITS.md; the text
is this library's.

Terms: lean/GLOSSARY.md.
"The text" (except in "the text is this library's"): a print of this protocol's technical report
(lean/CREDITS.md); it is not in this repository.
-/
import Cm.RelBase
import Cm.HeadHonest
import Cm.Rel2LayersHon

set_option autoImplicit false

/- no default table of scales is in sight in this file: what reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All
open Inst.Model.Layout (kRef hRef)

/-! ## Tables of scales, without a policy -/

/-- A table of scales: the words of the 48 layers and the final normalisation. -/
structure Scales where
  w : Fin 48 → Words
  nf : NormPar

namespace Scales
variable (s : Scales)

/-- the words of layer L, as the program reads them; beyond the last layer, which nobody reads, the
reference words -/
def kap : ℕ → LayerScale := fun L => if h : L < 48 then (s.w ⟨L, h⟩).scale else ppref.scale

/-- The table is lawful. -/
structure Lawful : Prop where
  /-- the shifts and the two normalisations of every layer: 5 ≤ kq, kk ≤ 32, equal unless both are
  16 or more; 1 ≤ kv, kg, kg', ku, ku' ≤ 24; 1 ≤ ko ≤ 19; 10 ≤ kd ≤ 19; 8 ≤ kr ≤ 24; for a
  normalisation 1 ≤ ϵ < 2^48, 24 ≤ M ≤ 47, 17 ≤ K ≤ 32, M ≤ K + 14 -/
  ff : ∀ L : Fin 48, FFSeg.Ranges (s.w L).scale
  /-- the shift of the attention gap -/
  sh : ∀ L : Fin 48, 4 ≤ (s.w L).sh ∧ (s.w L).sh ≤ 12
  /-- one value in a group of four layers -/
  one : ∀ g : Fin 12, ∀ l : Fin 4, (s.kap (4 * g + l)).sh = (s.kap (4 * g)).sh
  /-- the final normalisation -/
  nf : s.nf.OK
  /-- no normalisation shifts right by more bits than its reciprocal is scaled by -/
  km : (∀ L : Fin 48, (s.w L).n1.K ≤ (s.w L).n1.M ∧ (s.w L).n2.K ≤ (s.w L).n2.M) ∧ s.nf.K ≤ s.nf.M

end Scales

/-! ## Bounds -/

/-- what the head reads of a request: r, e, the checked tokens (at position t: token t + 1 of the
request; at the last position y). (The record's fourth field, a policy's words, is read by nothing
here.) -/
def reqOf (x : Instance ppref) : Head.Req := ⟨x.r, x.e, x.w, ⟨0, 0, 0⟩⟩

/-- every cell that some segment reads is below B in absolute value -/
structure Below2 (B : ℤ) (T : Trace) : Prop extends BelowL B T where
  hf : ∀ i < Head.nT, ∀ φ < Plain.nHf, |T.hf φ i| < B
  hd : ∀ i < Head.nT, ∀ φ < Head.nFeat .hd, |T.hd φ i| < B
  hr : ∀ i < Head.nT, ∀ φ < Plain.nHr, |T.hr φ i| < B

/-! ## The honest trace -/

/-- The cells that the honest prover computes. -/
def trace2 (s : Scales) (i : Idx) (x : Instance ppref) : Trace :=
  Lay.honTK s.kap s.nf (fun _ => tbRef) i.mat x.prompt
    (Plain.hon s.nf (Lay.xsK s.kap (fun _ => tbRef) i.mat x.prompt 11 8) i.weights.H (reqOf x))

end Cm
