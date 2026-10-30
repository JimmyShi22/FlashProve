-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ObjectGuardsSeeded.lean: four guards for the statements on the index's committed tables with OOD
seeds named by the environment (E2E/WholeViewTablesSeeded.lean, E2E/TablesAtOwnObject.lean).

What is shown.
  `demoS_adm` (with `demo_fits`, E2E/ObjectGuardsMore.lean): THE PREMISES ON THE ENVIRONMENT CAN BE
    MET BY ONE THAT ASKS FOR EVERYTHING: a typed environment that makes a copy at an OOD seed s of
    its own naming, runs the key file's protocol on the first table, the link on the copy, a batch
    on the copy with all its requests shown, reads a single symbol of the copy, and STOPS WITH ALL
    THAT IT WAS SHOWN (`Seen`, E2E/ObjectGuardsMore.lean), so that the statements' conclusion says
    something at it; it is admissible, all seeds allowed, at the bounds `demoB`, which fit the
    numbers 44,040,191 | 62 | 62 | 62 | 64. For every object.
  `tables_differ_own`: at `objOwn Z`, the object of the form to quote: two different matrices IN
    RANGE never have the same committed table with the same OOD sample (E2E/ObjectGuardsMore.lean's
    `tables_differ_uncut`, by one unfolding). Of all matrices that is false by the encoder's text
    (no theorem here says so): of a cell the encoder reads the first coordinate alone.
  `not_hidE_own`: at `objOwn Z`, every Z: at 44,040,192 columns the interface's clause on the
    encoder fails (E2E/TableHidesGuardAtFiles.lean's `not_hidE_filesAt`, by one unfolding; its
    limits stand).
  `reads_some_own`: at `objOwn Z`, Z in scope, where the IOP's own test on the public files accepts:
    the key file's verifier and one request's verifier of the proof file read at least one column
    (E2E/ReadsNotEmptyAtObject.lean's `reads_some_filesAt`, by one unfolding).

Limits. One environment. It names a fixed seed: an environment whose seed hangs on what it has seen
is of the same type and is not written here.

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.


-/
import E2E.ObjectGuardsMore
import E2E.TablesAtOwnObject
import E2E.TableHidesGuardAtFiles
import E2E.ReadsNotEmptyAtObject

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop Hiop.Seeded

section Demo
variable {I X : Type} (L : HolographicProtocol I X) (s : L.OutOfDomainSeed) (x : X) (p : Fin L.wordLength)

/-- Make a copy at the OOD seed s; run the key file's protocol on the first table; the link on the
copy; a batch on the copy, all its requests being x, and all shown; read the copy's symbol at p;
STOP WITH ALL THAT WAS SHOWN. -/
def demoEnvS : L.Rec → EnvS L (Seen L) := fun a₀ =>
  .fresh s fun a₁ => .test 0 fun v₁ => .link 1 fun v₂ =>
    .session 1 Finset.univ (fun _ => x) (fun _ => none) fun v₃ => .read 1 p fun y =>
      .stop (a₀, a₁, v₁, v₂, v₃, y)

/-- **It is admissible at the bounds `demoB`, all seeds allowed.** -/
theorem demoS_adm (a : L.Rec) :
    (demoEnvS L s x p a).Adm (demoB L.maxBatchSize) (fun _ => True) (fun _ => True) 0 UsedR.zero := by
  exact ⟨trivial, by simp [demoB], fun _ => ⟨Nat.zero_le _, by simp [demoB, UsedR.zero], fun _ =>
    ⟨le_rfl, le_rfl, by simp [demoB, UsedR.zero], fun _ =>
      ⟨le_rfl, by simp [demoB, UsedR.zero], (Finset.card_univ.trans (Fintype.card_fin _)).le,
        fun _ => trivial, fun _ _ _ => trivial, fun _ =>
          ⟨le_rfl, by simp [demoB, UsedR.zero], fun _ => trivial⟩⟩⟩⟩⟩

end Demo

/-- **At the very object of the form to quote: two different matrices IN RANGE never have the same
committed table with the same OOD sample.** So what `tables_own` calls equal in law is a law of
parts of values that, whole, tell such indices apart. -/
theorem tables_differ_own (Z : VerifierAndGoals.PublicFiles) : NeverShareOn (objOwn Z) inRange :=
  tables_differ_uncut (filesAt Z) (filesAt Z).fixedMessageProvers

/-- **At the very object of the form to quote: at one column more the interface's clause on the
encoder fails.** The clause is a premise of `tables_seeded` (E2E/WholeViewTablesSeeded.lean), from
which `tables_own` is proved; that the conclusion of `tables_own` fails at a budget of one column
more is not said. -/
theorem not_hidE_own (Z : VerifierAndGoals.PublicFiles) : ¬ AtPublicFiles.Table.HidE (objOwn Z) 44040192 :=
  AtPublicFiles.Table.not_hidE_filesAt Z (filesAt Z).fixedMessageProvers

/-- **At the very object of the form to quote**, at Z in scope where the IOP's own test on the
public files accepts: the key file's verifier and one request's verifier of the proof file read at
least one column of the committed table, at every instance and verifier randomness. -/
theorem reads_some_own (Z : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    (∀ x ρ, ((objOwn Z).offline.extReads x ρ).Nonempty) ∧
      ∀ x ρ, ((objOwn Z).onlineBatch.loc.extReads x ρ).Nonempty :=
  AtPublicFiles.Reads.reads_some_filesAt Z scope live (filesAt Z).fixedMessageProvers

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.demoS_adm
#print axioms AtPublicFiles.AtFiles.tables_differ_own
#print axioms AtPublicFiles.AtFiles.not_hidE_own
#print axioms AtPublicFiles.AtFiles.reads_some_own
