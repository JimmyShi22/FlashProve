-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/Rel.lean: the model with the head of Inst/Model/Head/, with the cells as witness: the bound on
cells, the honest trace, and the tables of exact match. Definitions; lemmas on them are in
Cm/RelProofs.lean.

Policy/Rel/LedgerRel.lean reads `Below`, Policy/Rel/LedgerRelLaws.lean `trace`. The plain head is
Cm/Rel2.lean; what the two share is Cm/RelBase.lean: the index (`Idx`, a well-formed digit matrix),
its weights, the bound of the layers, the true request (`TrueAt`). Told in the opening comment of
Cm/RelBase.lean, and true here as well: every well-formed choice of weight tensors (`Index ppref`)
is held by an index (`index_onto`, Cm/RelTrue.lean); by reading of the layout, and no theorem, the
map (`Idx.index`) is not one to one: entries at which no byte of a weight lies are free within the
two ranges of `WFW` (Inst/Model/Layout.lean).

Main names, for a table pp of scales and policy (a parameter of everything below, no part of an
index):
  requests and replies: `Instance ppref` of Inst/Model/Program.lean: 1,024 tokens, the announced
    token y, and r, e: the positions r ≤ t < e are covered; position t checks token t + 1, the last
    position checks y.
  cells: `All.Trace`: the integer cells of the 12 feed-forward segments, the 12 attention segments
    and the head.
  `Below B T`: every cell that some segment reads is below B in absolute value.
  `trace pp i x`: the honest trace (`All.honTK`), a named function of index and request.
  `ExactPol`, `Table`: the policies of exact match (θ = 2^8 ≤ C, and cap = 0 or 2^8 < C);
    `Table pp`: pp is lawful (Inst/Model/Scales.lean) and its policy is one of exact match.

Limits:
The head is not the plain one: it carries the programs' cost ledger also at exact match: six hidden
numbers for each position, a look-up of a further table, the term ρC (c + 2^37 b) in the margin of a
counted position (`Instance.cnt`, Inst/Model/ProgramR.lean). A head with the plain margin in three
digits at every covered position, and no policy anywhere, is that of Cm/Rel2.lean. There the table
has no policy (`Scales`), and `Below2`, `trace2` differ.
A wider family than the text's. The print has one shift of the attention gap for all layers. A
lawful table has one value in each group of four layers, free from group to group (4 to 12). So "for
every lawful table" ranges over more integer programs than that text defines; at a table with two
values of that shift the program here is none of the text's.
This file does not say that a table is sensible. "Lawful" asks K ≤ M of all 97 normalisations (shift
at most exponent) and 24 ≤ M; that shuts out tables at which a normalisation puts out 0 whatever its
input, so that, if it is the final one, token 0 is the first choice everywhere whatever the weights
(for instance exponent 10 with shift 16, which size conditions without a lower end on the exponent
admit). It does not shut out every idle table: the library from which the model's files are copied
exhibits a lawful table with the policy (2^8, 2^8, 0), so a Table, at which none of the 48 layers
adds anything to the stream whatever its weights (not copied here). At such a table a statement over
every lawful table says little of the weights. This file says nothing on codes, oracles or
protocols: the code's side of a configuration (encoding of an index, hold, held, what an encoded
index hides) is not here. It says nothing on segments as polynomial maps. It says nothing on any
fitted table or real weights: "for every lawful table" covers a fitted table only if it is lawful.
That "the integer program" is the model that the print describes is a comparison by reading of two
definitions, and no theorem. The type `All.Trace` has names that no segment reads; `Below` says
nothing of the values there, so different terms stand for one assignment of cells.
The notions (cells as witness, an honest and a relaxed bound on cells; and, in
Policy/Rel/LedgerRel.lean, a relation pair and conditions modulo p that force and admit the reply)
follow the worked example named in lean/CREDITS.md; the text is this library's.

Terms: lean/GLOSSARY.md.
"The print", "the text" (except in "the text is this library's"): a print of this protocol's
technical report (lean/CREDITS.md); it is not in this repository.
-/
import Cm.RelBase
import Inst.Model.All.HonestK
import Code.Field

set_option autoImplicit false

/- no default table of scales is in sight in this file: what reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All
open Inst.Model.Layout (kRef hRef)

/-! ## Cells and bounds -/

/-- every cell that some segment reads is below B in absolute value -/
structure Below (B : ℤ) (T : Trace) : Prop extends BelowL B T where
  hf : ∀ i < Head.nT, ∀ φ < Head.nFeat .hf, |T.hf φ i| < B
  hd : ∀ i < Head.nT, ∀ φ < Head.nFeat .hd, |T.hd φ i| < B
  hr : ∀ i < Head.nT, ∀ φ < Head.nFeat .hr, |T.hr φ i| < B

/-! ## The honest trace -/

/-- The cells that the honest prover computes. -/
def trace (pp : ScalesAndPolicy) (i : Idx) (x : Instance ppref) : Trace :=
  honTK pp.kap pp.nf (fun _ => tbRef) i.mat x.prompt (Head.Req.of pp.pol x)

/-! ## The tables of exact match -/

/-- a policy of exact match: θ = 2^8 ≤ C, and cap = 0 or 2^8 < C -/
def ExactPol (pol : AcceptancePolicy) : Prop := pol.theta = 2 ^ 8 ∧ 2 ^ 8 ≤ pol.C ∧ (pol.cap = 0 ∨ 2 ^ 8 < pol.C)

instance (pol : AcceptancePolicy) : Decidable (ExactPol pol) := by unfold ExactPol; infer_instance

/-- a lawful table of exact match -/
structure Table (pp : ScalesAndPolicy) : Prop where
  lawful : Lawful pp
  exact : ExactPol pp.pol

end Cm
