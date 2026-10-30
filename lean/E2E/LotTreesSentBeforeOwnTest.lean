-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- A lot's statement. No sorry.
/-
E2E/LotTreesSentBeforeOwnTest.lean.
It says: at the key file's own test on the last chain, the three trees that the test reads stand in the set of tables at hand, at the sources
taken 0 0, taken 0 5, taken 1 1: OwnAsks.opens' last clause (E2E/KeyOwnAccepted.lean:58). It is the twin of old_KR (Honest/K12/TreesSentBeforeTestAtKey.lean:169) at
three trees. opensFit_KW (KeyOwnOpens) pays the clause's other half. By a reading: true if the tables at hand are the sending parts' tables at their own
coins: the structure TablesAreLaid here, at the last thread's own tables.
Not tested.
Nothing on soundness, completeness, hiding or binding. No hostile reader has held this statement: the pen's first act
is to elaborate it and test it, not to prove it. A statement found false or unprovable as written
is not mended here.
-/
import E2E.KeyOwnAccepted
import E2E.KeyOwnOpens
import E2E.KeyJobW
import E2E.KeyDoorItems
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import E2E.KeyArgumentsAt
import E2E.KeyTreesKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

-- MENDED: «noncomputable section»: lotK and lotJob hang on offlineSenders, which is noncomputable. Nothing else is turned.
noncomputable section

namespace AtPublicFiles.KeyLastChain.Lots
open ProofFile.Honest ProofFile.Honest.K12
open H2K.Member (piKWFull)

/-- The sendings of the value: what the offline prover is handed at a description, in front of its four tests. -/
abbrev lotK (files : VerifierAndGoals.PublicFiles) (description : AtPublicFiles.AtFiles.HonestTerm.OfflineDescription) :
    AtPublicFiles.KeyFile.KeyParts AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness Unit Unit AtPublicFiles.KeyValues.WitK :=
  AtPublicFiles.AtFiles.HonestTerm.offlineSenders (files := files) description

/-- The own test's job at the value: withTests' own term. -/
abbrev lotJob (files : VerifierAndGoals.PublicFiles) (description : AtPublicFiles.AtFiles.HonestTerm.OfflineDescription) :=
  AtPublicFiles.KeyLay.jobKWAt description.source description.numbers description.later
    (lotK files description).idx (lotK files description).w (lotK files description).send id
    (ProofFile.Honest.K12.Light.askOf (lotK files description).send (fun w => (lotK files description).weights w.w₀)
      (fun w => AtPublicFiles.KeyFile.randK14 ((lotK files description).rand w.rc)))

/-- **The tables at hand are the ones that the last thread lays**, at the value (from reading
Thread.handAt, Thread.tableAt, tableLast, fixedLast, tbH and tbKey): what (H) gives at a stand: each table in E has the same columns as
the thread's, read at the challenges that its field fixed names. Tree index 0 at Omega: KeyTreesWritten's treesU QK = 1. -/
structure TablesAreLaid {Bk : ProverCoinCounts} (files : VerifierAndGoals.PublicFiles) (description : AtPublicFiles.AtFiles.HonestTerm.OfflineDescription) (k : Coins Bk)
    (v : Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness VerifiableInference.Desc.Key.Xi Unit) (heard : List Fmt.Drawn)
    (E : Env) : Prop where
  idx : ∃ u, E.tree (.taken 0 0) = some u ∧ u.2.same (ProofFile.Honest.K1.treeTbl 0 id (lotK files description).idx (lotK files description).own₀ 0 k v
    (heard.take (AtPublicFiles.KeyThread.sentIn (AtPublicFiles.KeyThread.decl₁ (VerifiableInference.Desc.Key.descriptionFromSource description.source
                          description.numbers description.later)) 0))).2 = true
  wTree : ∃ u, E.tree (.taken 0 5) = some u ∧ u.2.same (ProofFile.Honest.K1.treeTbl 0 id (lotK files description).w (lotK files description).own₀ 0 k v
    (heard.take (AtPublicFiles.KeyThread.sentIn (AtPublicFiles.KeyThread.decl₁ (VerifiableInference.Desc.Key.descriptionFromSource description.source
                          description.numbers description.later)) 5))).2 = true
  omega : ∃ u, E.tree (.taken 1 1) = some u ∧ u.2.same (ProofFile.Honest.K14.sendTable
    (ProofFile.Honest.K14.jobOmega ⟨(lotK files description).send.P, 0⟩)
    (ProofFile.Honest.K14.witOf (lotK files description).send.P (lotK files description).weights fun r => AtPublicFiles.KeyFile.randK14 ((lotK files description).rand r))
    (ProofFile.Honest.K14.sendPlace 5) 1 0 k (AtPublicFiles.KeyDoorItems.commonOf v)
    ((heard.take ((AtPublicFiles.KeyThread.decl₁ (VerifiableInference.Desc.Key.descriptionFromSource description.source description.numbers
                  description.later)).length + AtPublicFiles.KeyThread.sentIn (AtPublicFiles.KeyThread.decl₂ (VerifiableInference.Desc.Key.descriptionFromSource
                                      description.source description.numbers description.later)) 1)).drop
      (AtPublicFiles.KeyThread.decl₁ (VerifiableInference.Desc.Key.descriptionFromSource description.source description.numbers
                  description.later)).length)).2 = true

/-- **Lot P3, at the value.** The coins c are what the book lends at k's purses of the last chain; m is where the run stands. THE PEN's WORK IS THE TIE
through the book's carrying: a many-member twin of old_of_table, same_one, coinsTie_of_book, which stand at jobOne alone (the compiler-turns thread's word; WMemberSent,
SendersW stand at jobRealW and do not plug in at jobKW); AND two owed reads: batchedRowsSending's data reads nothing from number sentIn decl₁ 5 on (K1 has no readsBelow yet); tree 1's fresh
rows are those of W's table. Tree 0 of Omega's sentTables: o_omega's alone, by a reading of sendings_count (treesOf5 QK = 2, one tree a message): the pen holds it. -/
def LotOldAtOwnTest {V : Type} (files : VerifierAndGoals.PublicFiles) (description : AtPublicFiles.AtFiles.HonestTerm.OfflineDescription)
    (K₀ : AtPublicFiles.KeyBook.KeyPub) (k : Coins (AtPublicFiles.KeyBook.keyBook K₀))
    (m : Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness VerifiableInference.Desc.Key.Xi Unit) Unit) (E : Env)
    (c : RowCoins [(firstPart (lotJob files description).toRun.toTest :
        Part V (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness VerifiableInference.Desc.Key.Xi Unit) Unit),
      restPart (lotJob files description).toRun.toTest]) : Prop :=
  VerifierAndGoals.InScope files = true →
  AtPublicFiles.AtFiles.KeySourced files description.source description.numbers description.later →
  AtPublicFiles.AtFiles.HonestTerm.offlineDescription files = .ok description →
  AtPublicFiles.KeyBook.fullPub = some K₀ →
  (lotJob files description).toRun.toTest.p = piKWFull →
  lendRow (AtPublicFiles.KeyBook.keyBook K₀) ((AtPublicFiles.KeyBook.keyBook K₀).rowsOf 2) (k.look 2) (lotJob files description).toRun.toTest.p.place
    [(firstPart (lotJob files description).toRun.toTest :
        Part V (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles files).EncodingRandomness VerifiableInference.Desc.Key.Xi Unit) Unit),
      restPart (lotJob files description).toRun.toTest] 0 = .ok c →
  TablesAreLaid files description k m.st.input m.st.heard E →
  OldAt E ((lotJob files description).toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins (lotJob files description).toRun.toTest c.2.1).mem
      ((lotJob files description).toRun.toTest.first m.st.input (frontOf m) (restCoins (lotJob files description).toRun.toTest c.2.1)))
    (fun k => [Fmt.TreeSource.taken 0 0, .taken 0 5, .taken 1 1].getD k (.own 0))

end AtPublicFiles.KeyLastChain.Lots
