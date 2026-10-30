-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/ReadyAtFiles.lean: at every pair of the relation at Z (`RyesZ Z`, E2E/TiedAtFiles.lean) the
model's own trace (`Cm.trace`, Cm/Rel.lean) is a witness of the library's strict relation. `Serves`
is a definition: two of the tests that a prover structure H (`ProofFile.Honest.Prover`,
Johnson/Desc/ProofFile/Honest/Frame.lean) has to pass so that `ProofFile.Honest.ready` (same file)
returns, asked at every pair of that relation. General in the three public files Z; `Serves` also in
H and in its types Rc, Tr, X₀ and Xh. One definition, statements and proofs; nothing is evaluated.

For what. `RyesZ Z` is the model's relaxed relation: some trace meets the conditions, with every
cell that a segment reads below 2 ^ 18 in absolute value. The strict relation asks the same with the
bound 129. An honest prover computes one trace, the model's own. If the relaxed relation held of a
request at which the model's own trace is no witness, an honest prover would have no witness there.
That does not happen: the library shows that the two relations have the same language, at every
lawful table of scales and policy (`ledger_lang`, Policy/Rel/LedgerRelLaws.lean), and the table that
its reader returns at two files is lawful at all files.

  `strict_of_ryesZ`: from `RyesZ Z M x'`: M is in range, and M holds an index at which `Cm.trace`
    meets the strict relation with the cost ledger (`Policy.LedgerRel.Ryes`), at the protocol's
    prime (`Cb.Gl.p`) and at Z's table (`ppAtFiles`): the table of scales and policy that the
    library's reader `settingsAtRef` returns at Z's files `pol` and `KL`, and the reference's table
    where it refuses
  `Serves Z H`: a definition, a structure of two fields. `range`: `H.inRange` accepts every matrix
    in range. `trace`: for every pair (M, x') of the relation and every OOD sample rec (`RecFull`:
    an out-of-domain seed with answers), `H.trace` returns a trace at M and at what
    `LPFD.Full.instanceAsPlainRecord` writes for (x', rec)
  `Serves.both`: under `Serves Z H`, both hold at every pair of the relation, at every OOD sample

By what. `ryesZ_iff` (E2E/TiedAtFiles.lean) writes `RyesZ Z` out. `ledger_forces`: every witness of
the relaxed relation shows `RinfPP pp` at the index. `ledger_trace_iff`: `Cm.trace` is a witness of
the strict relation just where `RinfPP pp` holds. Both are in Policy/Rel/LedgerRelLaws.lean, for a
prime of at least 2 ^ 61 - 1 and a table with `LedgerRel.TableOK`; for these two conditions:
`ledger_gl_big`, `tableOK_of_lawful` (same file), `Code.pGold_prime` (Code/Field.lean) and
`lawful_ppAtFiles` (Johnson/Flat/PolicyAtFrame.lean). `Serves.both` is by the two fields and
`ryesZ_iff`.

Limits.
- `Serves` is a hypothesis on H: no prover structure is defined here. `strict_of_ryesZ` says that a
  trace which such a prover can return exists and is the model's own. That a given H returns it has
  to be shown by whoever defines H: H reads the matrix and the written instance (bytes), so it has
  to find the index in the matrix and read the request back.
- `Serves` does not give `ProofFile.Honest.ready … = .ok`. The other tests of `ready` are not asked here:
  that each part of the prover's (`Placed`) is at the place of a sub-protocol of its chain and no
  two are at one place, the description's own test on the places (`placesOk`), `H.inRange H.dummy`,
  the test on the book of coins (`ProverCoinCounts.word`), and that `chainSteps` returns for the three chains.
  Whether these pass depends on neither the index nor the instance (for `chainSteps`:
  `chainSteps_any`). `rowsAt_of` (E2E/BridgeJoinAtFiles.lean) takes them from one return of `ready`,
  by `ready_any` (both lemmas: Honest/Law/ReadyAny.lean).
- The field `trace` of `Serves` is asked at every OOD sample, also at those that are not the
  matrix's own (`recAt`, E2E/TiedAtFiles.lean: an OOD seed with the OOD answers of the matrix at
  that seed and at the committer's coins).
- That the prover's parts in H accept that trace is not stated.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.TiedAtFiles
import Policy.Rel.LedgerRelLaws
import Johnson.Flat.PolicyAtFrame

set_option autoImplicit false

namespace AtPublicFiles.Committed
open VerifiableInference.OnPublicFiles (numsRef ppAtFiles)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles asDescriptionFiles)
open AtPublicFiles.AtFiles
open Inst.Model

/-- **At every pair of the relation at Z the model's own trace is a witness of the strict
relation.** `RyesZ Z` is the relaxed relation; its language is the strict relation's. -/
theorem strict_of_ryesZ (Z : PublicFiles) (M : FullSizeMatrix) (x' : XF) (h : RyesZ Z M x') :
    inRange M ∧ ∃ idx : Cm.Idx, VerifiableInference.OnPublicFiles.Flat.Holds M idx ∧
      Policy.LedgerRel.Ryes Cb.Gl.p (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL) idx x'.val
        (Cm.trace (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL) idx x'.val) := by
  obtain ⟨hr, idx, hH, T, hT⟩ := (ryesZ_iff Z M x').1 h
  have hok := Policy.tableOK_of_lawful
    (VerifiableInference.OnPublicFiles.lawful_ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL)
  exact ⟨hr, idx, hH,
    (Policy.ledger_trace_iff Code.pGold Code.pGold_prime Policy.ledger_gl_big _ hok idx x'.val).2
      (Policy.ledger_forces Code.pGold Code.pGold_prime Policy.ledger_gl_big _ hok idx x'.val T hT)⟩

section Serves
open ProofFile.Honest (Prover)
open OnBytes (TableKey)
variable {Rc Tr X₀ Xh : Type}

/-- Two of the tests of `ProofFile.Honest.ready`, the two whose outcome can depend on the index or the
instance, at every pair of the relation at Z: the prover's test on the index accepts every matrix in
range; the prover has a trace at what is written for every pair of the relation, at every OOD
sample. -/
structure Serves (Z : PublicFiles) (H : Prover FullSizeMatrix Rc ProofFile.Inst TableKey Tr X₀ Xh) : Prop where
  range : ∀ M : FullSizeMatrix, inRange M → H.inRange M = true
  trace : ∀ (M : FullSizeMatrix) (x' : XF) (rec : OnBytes.Flat.RecFull), RyesZ Z M x' →
    (H.trace M (LPFD.Full.instanceAsPlainRecord (x', rec))).isSome = true

/-- Both fields of `Serves` at a pair of the relation and an OOD sample. -/
theorem Serves.both {Z : PublicFiles} {H : Prover FullSizeMatrix Rc ProofFile.Inst TableKey Tr X₀ Xh} (S : Serves Z H)
    {M : FullSizeMatrix} {x' : XF} (rec : OnBytes.Flat.RecFull) (h : RyesZ Z M x') :
    H.inRange M = true ∧ (H.trace M (LPFD.Full.instanceAsPlainRecord (x', rec))).isSome = true :=
  ⟨S.range M ((ryesZ_iff Z M x').1 h).1, S.trace M x' rec h⟩

end Serves

end AtPublicFiles.Committed

#print axioms AtPublicFiles.Committed.strict_of_ryesZ
#print axioms AtPublicFiles.Committed.Serves.both
#print axioms AtPublicFiles.Committed.Serves
