-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/K9RowsAsk.lean: ONE TEST WITH CODE ON PUBLIC NUMBERS, A SEGMENT AT A TIME:
"THE ROWS FIT": the plan's number of claims, the indices that the ties take and the indices that
the reads take are together at most the rows that the batching's declared round has.
Definitions alone. No Mathlib. For the cutting-in as a conjunct
of the test `k9Entry` (Johnson/Desc/First/Link/K9Asks.lean): the places with rounds are handed in,
made once by the caller.

  `firstB tl`: the indices that the ties take: over the matrices, stepF times the matrix's rows of
    symbols rounded up to a power of two.
  `readsB NM mats ps`: the number of reads: over the matrices mu < NM, over the tables of ps
    (matrix, rows in a block) on mu: the matrix's rows over the table's rows in a block.
  `layPairs`, `attPairs`, `headPairs`: the tables of a layers' segment, of an attention segment and
    of the head, each as (matrix, rows in a block): off the public parameters alone.
  `pairsAt W l`, `claimsAt W l`: by the segment's number: even below 24: layers; odd: attention;
    24: the head. THE CALLER ASKS l < 25 ALONE: at a greater l the arms are the layers' and the
    attention's, at groups that are not there.
  `rowsFitB xs Z l X`: **THE TEST**: claims + (firstB X.tl + readsB .. * stepF) ≤ the declared rows.
    xs: `ProofFile.k9Stretches Z`, made once by the caller.
EVERY "none" ENDS IN false: no plan of the group; no table can be laid; no declared round.
SECOND TEXTS: `layPairs` repeats `layShapes` (OnBytes/Tie/Pv/Tail/ShapesLay.lean); `attTriples`
repeats `attAsks` (ShapesAtt.lean); `headTabs` repeats `tabsOfPlan`
(Johnson/Desc/Kinds/Law/TablesPlanCode.lean); `firstB` repeats `firstOf`
(OnBytes/Tie/Pv/Tail/EndLoopsB.lean): they will have to be turned with the texts that they repeat.
The ties are in Law/K9RowsAskLaw.lean.
LOOPS OVER A PUBLIC NUMBER: List.range tl.NM, List.range S.cf.NAs, `repB k`: safe only behind the
rows of the entry tests that hold these numbers.
POWERS OF TWO. 2 ^ clog2 x is below 2 x. FIVE POWERS HAVE A PUBLIC EXPONENT AND NO GUARD HERE. The
reason, BY READING: the maker of Z has computed each of them before any entry test runs (Z.p.X is
the return of `publicOf`; each planner returned), and each reaches the maker's output or a test on
which it branches:
  2 ^ h.la: OnBytes/Model/HeadPlan.lean: `readsLength` (the field nU) and `readsH` (nLin, rows);
  2 ^ h.lmbH: HeadPlan.lean: `matsH`: the stored matrix bH's rows;
  2 ^ cf.lmS: OnBytes/Model/AttentionPlan.lean: the stored matrices "as"' rows;
  2 ^ cf.lmb: AttentionPlan.lean: the stored matrix bA's rows;
  2 ^ cf.la: OnBytes/Model/AttentionShape.lean: the test of a refusal; AttentionPlan.lean:
    `tableReads` (the field own.rows).
No row of the entry tests is named here as holding the exponents.
DEFAULTS: `getD … {}` at a number that is not there gives an empty matrix or shape (m = 0, mS = 0).
`layPairs` reads `P.tails.getD g {}`: at a g beyond that list: an empty list of matrices, NOT a
"none": `claimsAt`'s `W.G[l / 2]?` stands guard beside it; that the two lists are equally long is
said nowhere. A table with 0 rows in a block counts 0 reads (x / 0 = 0).
Limits. A yes says what the clause says and no more.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Model.StagesLinks
import OnBytes.Model.Tail
import OnBytes.Model.LayerForms
import OnBytes.Model.AttentionScores
import Johnson.Desc.ProofFile.Pub
import Johnson.Desc.ProofFile.Lot.K9
import Johnson.Desc.Own.HeadTabs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model

/-- The indices that the ties take. -/
def firstB (tl : HTailF2) : Nat :=
  (List.range tl.NM).foldl (fun n nu => n + tl.stepF * 2 ^ clog2 (tl.shp.getD nu {}).mS) 0

/-- The number of reads. -/
def readsB (NM : Nat) (mats : Array TMat) (ps : List (Nat × Nat)) : Nat :=
  (List.range NM).foldl (fun n mu =>
    n + ps.foldl (fun k t => k + if t.1 = mu then (mats.getD mu {}).m / t.2 else 0) 0) 0

/-- A layers' segment's tables. -/
def layPairs (P : Layer.Pub) (g : Nat) : Option (List (Nat × Nat)) :=
  (Layer.layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k))
    (Layer.tableAsks P.y P.rd g) 0).map fun x => x.2.1.flatMap fun a => a.2.map fun m => (m.1,
    a.1.L)

/-- A list k times. -/
def repB : Nat → List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | 0, _ => []
  | k + 1, l => l ++ repB k l

/-- An attention segment's tables at k units of the scores: matrix, rows in a block, entries. -/
def attTriples (S : Attention.Shape) (k : Nat) : List (Nat × Nat × Nat) :=
  let asP : List (Nat × Nat × Nat) :=
    (List.range S.cf.NAs).flatMap fun q => [(q, 2 ^ S.cf.lmS, S.kAs / S.cf.NAs)]
  let row := (S.cf.NAs, S.T, S.fillH)
  let q := (S.cf.NAs + 3, 2 ^ S.cf.la, S.fillQ * S.T / 2 ^ S.cf.la)
  let b := (S.cf.NAs + 2, 2 ^ S.cf.lmb, S.kbA)
  asP ++ (asP ++ (asP ++ (repB k [row] ++ ([row] ++ ([row] ++ ([row] ++ ([row] ++
    ([row] ++ ([row] ++ ([(S.cf.NAs + 1, 2 ^ S.cf.la, S.fillO * S.T / 2 ^ S.cf.la)] ++
    (repB k ([q] ++ [q]) ++ ([q] ++ ([q] ++ ([q] ++ ([q] ++ ([q] ++ ([b] ++ ([b] ++
    ([b] ++ [])))))))))))))))))))

/-- The number of the units of the scores. -/
def unitsB (S : Attention.Shape) : Nat :=
  (Attention.unitsOf S Attention.Table.kfd [Attention.Seg.fm, Attention.Seg.fd]).length

def attPairs (S : Attention.Shape) : List (Nat × Nat) :=
  (attTriples S (unitsB S)).map fun a => (a.1, a.2.1)

/-- The head's tables without their weights. -/
def headTabs (h : Head.Shape) (hp : Head.HPlanH2) : Option Head.Tables :=
  ([(0, h.NHf, 2 ^ h.la, "hf@Z"), (0, h.NHf, 2 ^ h.la, "hf@phiZ"),
    (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, "xbL@Z_V"), (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, "xbL@Y_N"),
    (h.NHf, 1, h.T, "hd@zt_FC"), (h.NHf, 1, h.T, "hd@r_H"),
    (h.NHf + 1, 1, h.T, "hr@zt_ROW"), (h.NHf + 1, 1, h.T, "hr@P_V"),
    (h.NHf + 1, 1, h.T, "hr@r_tV"), (h.NHf + 1, 1, h.T, "hr@rt_N"),
    (h.NHf + 1, 1, h.T, "hr@phiC"), (h.NHf + 1, 1, h.T, "hr@rhoC"),
    (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, "bH-bits-0"), (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, "bH-bits-1"),
    (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, "bH-pin")] : List (Nat × Nat × Nat × String)).foldlM
    (fun t a => Own.tableAdded hp.tl.mats t a.1 a.2.1 a.2.2.1 #[] a.2.2.2) {}

def headPairs (h : Head.Shape) (hp : Head.HPlanH2) : Option (List (Nat × Nat)) :=
  (headTabs h hp).map fun t => t.funs.toList.map fun Fn => (Fn.mat, Fn.len)

/-- The segment's tables. -/
def pairsAt (W : Verify.Public) (l : Nat) : Option (List (Nat × Nat)) :=
  if l = 24 then headPairs W.hS W.H
  else if l % 2 = 0 then layPairs W.layers (l / 2)
  else (W.A[l / 2]?).map fun a => attPairs a.S

/-- The plan's number of claims. -/
def claimsAt (W : Verify.Public) (l : Nat) : Option Nat :=
  if l = 24 then some W.H.nLin
  else if l % 2 = 0 then (W.G[l / 2]?).map (·.nLin)
  else (W.A[l / 2]?).map (·.nLin)

/-- **THE TEST.** -/
def rowsFitB (xs : List (ProofFile.Spot × List Fmt.DeclaredRound × Nat)) (Z : ProofFile.Pub) (l : Nat)
    (X : Stages.LinkH) : Bool :=
  match claimsAt Z.p.X l, pairsAt Z.p.X l, ProofFile.k9Where xs l with
  | some n, some ps, some p =>
    decide (n + (firstB X.tl + readsB X.tl.NM X.tl.mats ps * X.tl.stepF) ≤ p.rows)
  | _, _, _ => false

end VerifiableInference.Desc.K9Asks
