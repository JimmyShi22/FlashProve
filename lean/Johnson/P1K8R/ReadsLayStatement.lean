-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ReadsLayStatement.lean: AT A LAYERS' SEGMENT THE READS THAT THE PUBLIC TEST `rowsFitB`
("the rows fit", Johnson/Desc/First/Link/K9RowsAsk.lean) COUNTS OFF THE SEGMENT's TABLES ARE AT MOST
THE PLANNER's OWN COUNT `Layer.readsCount` (OnBytes/Model/LayerPlan.lean). STATEMENTS ALONE: three
definitions of propositions; no definition of another kind. NOTHING IS PROVED IN THIS FILE, and none
is one of the library's goals: they are lemmas' statements.

  `PairsSum`      GENERAL, on the library's laying of tables (`Layer.layTables`,
                  OnBytes/Model/LayerForms.lean): under any function of a matrix's number and a
                  block's rows, the sum over the pairs that are laid is the sum over the families,
                  and in each over its parts from the first on
  `ReadsLayOf`    GENERAL IN THE LAYOUT; IT NAMES NO PUBLIC RECORD: at a group g of a layout y whose
                  number of positions is 2 ^ lt, at a list of matrices with the rows and columns
                  of the layout's own (`matsR`, Johnson/Road/FormsKeysRun.lean), where the laying
                  returns: the sum over the pairs of "the matrix's rows over the block's rows" IS
                  `readsCount y rd g`
  `ReadsLay`      IN THE GOALS' SCOPE, at a layers' plan hp, number g, of the public record: the
                  segment's pairs (`layPairs`) are there, and `readsB` at the plan's own matrices
                  is at most `readsCount`

WHAT IT IS FOR. `rows_join` (Johnson/Desc/First/Link/Law/K9RowsParts.lean) has the test's left side
at most the plan's rows from four premises; the third statement is its premise on the reads at a
layers' segment. The like at an attention segment is `reads_att` of that file; at the head
`reads_head` (Law/K9ReadsHeadPaid.lean).

WHAT IT IS NOT. NOT THE TEST's YES AT ANY SEGMENT: that the declared round's rows are at least the
plan's is not here. No verifier asks the test. The second statement is an equation on a sum;
`readsB` itself counts a pair only where its matrix's number lies below NM: so the third says "at
most".

Limits. Counts on public data. Nothing on any property.
-/
import Johnson.Desc.First.Link.K9RowsAsk
import Johnson.Road.FormsKeysRun
import Johnson.Goal.Meaning.Pub34Scope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Lay Reads TableAsk TableAt layTables tableAsks readsCount)
open OnBytes.Road (matsR)
open VerifiableInference.Desc.K9Asks (layPairs readsB)

/-- The statement on the laying. Not proved here; a lemma's statement, none of the library's goals.
-/
def PairsSum : Prop :=
  ∀ (mats : Array (ℕ × ℕ)) (f : ℕ → ℕ → ℕ) (asks : List TableAsk) (p : ℕ)
    (x : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ), layTables mats asks p = some x →
    ((x.2.1.flatMap fun a => a.2.map fun m => (m.1, a.1.L)).map fun t => f t.1 t.2).sum =
      (asks.map fun a => ((List.range a.parts).map fun q => f (a.M0 + q) a.L).sum).sum

/-- The statement at a layout. Not proved here; a lemma's statement, none of the library's goals. -/
def ReadsLayOf : Prop :=
  ∀ (y : Lay) (rd : Reads) (g : ℕ) (mats : Array TMat)
    (x : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ), g < y.NGr → y.T = 2 ^ y.h.lt →
    (mats.map fun M => (M.m, M.k)) = matsR y g →
    layTables (matsR y g) (tableAsks y rd g) 0 = some x →
    ((x.2.1.flatMap fun a => a.2.map fun m => (m.1, a.1.L)).map fun t =>
      (mats.getD t.1 {}).m / t.2).sum = readsCount y rd g

/-- The statement in scope. Not proved here; a lemma's statement, none of the library's goals. -/
def ReadsLay : Prop :=
  ∀ (Pb : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : Option ByteArray) (X : Verify.Public) (g : ℕ)
    (hp : Layer.HPlan2), VerifierAndGoals.InScope Pb = true → VerifierAndGoals.readFiles Pb = .ok pp →
    Verify.publicOf Pb.pol Pb.KL lay = .ok X → X.G[g]? = some hp →
    ∃ ps, layPairs X.layers g = some ps ∧
      readsB hp.tl.NM hp.tl.mats ps ≤ readsCount X.layers.y X.layers.rd g

end P1K8

#print axioms P1K8.PairsSum
#print axioms P1K8.ReadsLayOf
#print axioms P1K8.ReadsLay
