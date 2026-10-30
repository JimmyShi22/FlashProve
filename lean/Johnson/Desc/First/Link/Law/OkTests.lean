-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OkTests.lean: THE CLAUSES OF THE PROMISE Ok ON WHICH THE EIGHT FIELDS
"fu…" OF THE THREE SORTS' TAKES REST (PayLayers.lean, PayAttention.lean, PayHead.lean; FullEq.lean),
AS TESTS WITH CODE ON WHAT IS FIXED BEFORE THE DRAW; EACH WITH "ITS YES GIVES THE CLAUSE's BODY";
AND THE SEVEN SISTERS' COMMON END FROM THESE. Definitions with code, and theorems. A law file; no
running text imports it. The tests with their "yes gives" stand, moved by program, in
OkClauseTests.lean beside this file; here stand the two starred theorems.

The tests read: tl (the approximate range proof's structure, as the promise holds it), funs (the
list of tables), F (the snapshot's ledger), a list of forms. None reads a table's weights phi.
  `blocksB tl`, `blocks_of_test`     FullEq.lean's okBlocks' body.
  `posB tl funs F`, `pos_of_test`     okPos' body.
  `apartAtB tl t`, `apart_at`         okApart's body at an array t ("∀ k" at `zOf k`: zOf is the
                    first call at 0 and the second at every other number: `zOf_two`).
  `apartB tl`, `apart_of_test`        okApart's body AT EVERY LIST OF TABLES: a read's table is
                    vector 0 or 2 (`reads_tree`, OnBytes/Tie/Pv/Tail/EndWhole.lean): the test asks
                    both.
  `uB tl i`         the array of the reads is vector 2 of the structure's list.
  `entsB i F l`, `ents_of_test`       every entry that a form of l names stands at array i, virtual
                    row 0, at a column below the ledger's width.
  `unitAt_full`     ⋆ AT A FULL STATE (`FullAt nU`): a table's vector, apart from the other sorts,
                    of the kind "table", with a row, is a unit at its first virtual row (`UnitAt`,
                    EntryUnit.lean): the third part of FullEqUnit.lean's fuEq_full2, by itself.
  `ent_of_tests`    ⋆⋆ THE SEVEN SISTERS' COMMON END: for whatever entries a kind names: the entry
                    in the world at a full state that goes on from q is `entUnit q y` (fixed by q
                    and the data): by EntryUnit.lean's hFu_of.
`ent_of_tests` HAS THE PREMISE `shape` (the kind is "table"; 0 < R, at the full state's ledger):
NOT HAD FROM `Fx9` AS IT STANDS ("goes on" carries the widths alone): TRUE ONLY WHERE EMPTY UNTIL
"goes on" CARRIES THE LOOKS. Then it follows from a test on the snapshot's looks.

Limits. Implications. Nothing is evaluated here. That a reached state's promise holds these yeses is
not said. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.Link.Law.FullEqUnit
import Johnson.Desc.First.Link.Law.OkClauseTests
import OnBytes.Tie.Pv.Tail.EndWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail (reads_tree)
open OnBytes.Tie.Pv.Tail.Port (readsList uOf posOf colsU UApart hasRow shapeAt coefficientsF_shape)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (selfTestP rkSelfTestP coefBody)
open VerifiableInference.Desc.First.TailClaims.Law (blank coefBody_all)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (UnitAt entUnit hFu_of)

/-! ## 2 At a full state -/

/-- ⋆ **At a full state a table's vector with a row is a unit at its first virtual row.** -/
theorem unitAt_full (nU : Array ℕ) (t : S) (b : K9.Part) (ts : HTailF2) (hfull : FullAt nU t)
    (hb : atS.get? t = some b) (hts : t.tl? = some ts) (n0 tU : ℕ) (hn : n0 < 3)
    (h0 : 0 < nU.getD n0 0) (hU : ts.ix.U.getD n0 none = some tU) (hZ : ts.ix.ZZ ≠ tU)
    (hB : ts.ix.BZ ≠ tU) (hS : ∀ mu, mu < ts.NM → ts.gtTree.getD mu 0 ≠ tU)
    (hP : ∀ k p, p ∈ (ts.zOf k).pieces.toList → p.tree ≠ tU)
    (hk : ((b.F.trees.getD tU {}).kind == HKind.table) = true)
    (hR : 0 < (b.F.trees.getD tU {}).R) : UnitAt b.F tU 0 := by
  obtain ⟨e, he⟩ := hfull
  obtain ⟨F, tl, g, hF, htl, hg, hself, h3, rfl⟩ := k8Tests_ok nU e _ he
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (part_back e tl _ b hb)
  obtain ⟨a₁, ha₁, f1, _, _, f4, _, _⟩ := get_put e a ha tl (coefBody tl g F)
  have eb : a₁ = b := Option.some.inj (ha₁.symm.trans hb)
  subst eb
  have et : tl = ts := Option.some.inj (f4.symm.trans hts)
  subst et
  let c : Ctx := { ch := { dry := false, entries := [] } }
  have hrun := coefF_runs tl g hg F c
  obtain ⟨k1, _⟩ := coefficientsF_shape tl F _ c c hrun
  rw [f1, coefBody_all] at hk hR ⊢
  have k := k1 tU
  unfold shapeAt at k
  have kk : (((Fo.coefAll tl g F).trees.getD tU {}).kind) = (F.trees.getD tU {}).kind :=
    congrArg (·.1) k
  have kR : (((Fo.coefAll tl g F).trees.getD tU {}).R) = (F.trees.getD tU {}).R :=
    congrArg (·.2.1) k
  exact unitAt_run tl n0 tU F _ c c
    ⟨Nat.lt_succ_of_lt hn, hU, hasRow_of_selfTest tl nU F hself n0 hn _ hU h0,
      by rw [← kk]; exact hk, hZ, hB, hS, hP⟩ (by rw [← kR]; exact hR) hrun

/-! ## 3 The seven sisters' common end -/

variable {β K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

/-- ⋆⋆ **For whatever entries a kind names: the entry at a full state that goes on from q is fixed
by q and the data.** Named: which entries the kind's forms name at q. -/
theorem ent_of_tests (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (Named : Q β → Ent → Prop)
    (okEnts : ∀ q x, Ok q → Named q x →
      ∃ tlb, (pi8 q.1).1 = some tlb ∧ tlb.ix.U.getD 2 none = some x.tree ∧ x.row = 0)
    (okThere : 0 < nU.getD 2 0)
    (okApart : ∀ q tlb tU, Ok q → (pi8 q.1).1 = some tlb → tlb.ix.U.getD 2 none = some tU →
      tlb.ix.ZZ ≠ tU ∧ tlb.ix.BZ ≠ tU ∧ (∀ mu, mu < tlb.NM → tlb.gtTree.getD mu 0 ≠ tU) ∧
        ∀ k p, p ∈ (tlb.zOf k).pieces.toList → p.tree ≠ tU)
    (shape : ∀ q t b tlb tU, Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
      (pi8 q.1).1 = some tlb → tlb.ix.U.getD 2 none = some tU →
      ((b.F.trees.getD tU {}).kind == HKind.table) = true ∧ 0 < (b.F.trees.getD tU {}).R) :
    ∀ q t b (y : Bound K), Fx9 (phiAll u ψ) Ok q t → FullAt nU t → atS.get? t = some b →
      ∀ x, Named q x →
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = entUnit q y x.tree x.row x.idx := by
  intro q t b y hf hfull hb x hx
  refine hFu_of ρ (phiAll u ψ) Ok (FullAt nU) Named
    (fun q k r => ∃ tlb, (pi8 q.1).1 = some tlb ∧ tlb.ix.U.getD 2 none = some k ∧ r = 0)
    (fun q x hOk hN => okEnts q x hOk hN) ?_ q t b y hf hfull hb x hx
  intro q t b hf hfull hb k r hun
  obtain ⟨tlb, h1, h2, rfl⟩ := hun
  obtain ⟨s2, s3⟩ := shape q t b tlb k hf hfull hb h1 h2
  obtain ⟨a3, a4, a5, a6⟩ := okApart q tlb k hf.1 h1 h2
  have hφ : phiAll u ψ t = q.1 := hf.2.1
  have e1 : (t.tl?).map (blank u) = some tlb := by
    have : (pi8 (phiAll u ψ t)).1 = some tlb := by rw [hφ]; exact h1
    exact this
  obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.1 e1
  exact unitAt_full nU t b ts hfull hb hts 2 k (by decide) okThere h2 a3 a4 a5 a6 s2 s3

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pos_of_test
#print axioms VerifiableInference.Desc.LinkJoin.apart_at
#print axioms VerifiableInference.Desc.LinkJoin.apart_of_test
#print axioms VerifiableInference.Desc.LinkJoin.ents_of_test
#print axioms VerifiableInference.Desc.LinkJoin.unitAt_full
#print axioms VerifiableInference.Desc.LinkJoin.ent_of_tests
