-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/BothEndsAtOneTerm.lean

This file puts completeness (CompleteOnServedRequests) and honest-verifier zero knowledge
(ZeroKnowledgeOnServedRequests) of the interactive oracle proof into one statement about the same
public files and the same provers, together with the equation that relates the two ways in which
these provers are written. It has no definition of its own.

Why one statement. complete_in_scope speaks of theProvers Z (settingsOfRead pp) (thePartsAt Z),
the provers that refuse a request that is not served. zkOnServedRequests_inScope takes as its
argument the provers without the refusal, HonestProvers.ofThreeProvers (honestProvers Z (thePartsAt Z)),
and by the definition of ZeroKnowledgeOnServedRequests it speaks of proversAtFiles Z hr applied to
them, which adds the refusal at ServedRequest. The third clause below says that the two are equal.
All three clauses are at the same Z, the same hr and the same thePartsAt Z.

Main statements.
  * bothEnds_in_scope: let Z be public files in scope (InScope Z = true) that pass protocolDataWellFormed, the
    verifier's first test on public files, and read as pp (hr). Then three things hold. First,
    CompleteAtFiles Z (thePartsAt Z) hr, which is CompleteOnServedRequests of theProvers; and
    there are numbers a and c with a + 0 + c ≤ completenessTarget (2^-41) at which
    CompleteAtEveryCoin holds of the same provers on ServedRequest. Second,
    ZeroKnowledgeOnServedRequests Z hr (HonestProvers.ofThreeProvers (honestProvers Z (thePartsAt Z))) at
    offlineStops = 0, linkStops = 0 and onlineStops = 2^-174. Third, theProvers Z (settingsOfRead
    pp) (thePartsAt Z) = proversAtFiles Z hr (HonestProvers.ofThreeProvers (honestProvers Z (thePartsAt
    Z))).
  * bothEnds_at_the_stored_files: the same at Z = VerifierAndGoals.storedPublicFiles, the stored full-size files, from
    their reading hr alone.

Limits.
  * The names of the definitions mean exactly what the definitions say. The sentences in this
    header summarise them and do not replace them.
  * Honest verifier; interactive oracle proof; the relation in both properties is ServedRequest.
    Everything here is before any hashing or compilation.
  * This file adds no statement on what a proof hides beyond ZeroKnowledgeOnServedRequests, as
    defined in VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean.
  * A statement of the form ZeroKnowledgeOnServedRequests alone is also met by a prover that stops
    publicly or sends fixed messages. This file states it beside completeness for the same
    provers. It does not derive the corollary that each of the three provers stops publicly with
    small probability (a bound that would follow from completeness at one served request). So this
    file does not itself exclude that the second clause is met vacuously, by provers that stop
    publicly.
  * A request at which the model has no result, or a result other than the claimed output, lies
    outside ServedRequest, and the first clause says nothing about it. The next three points are
    about the second clause and the definition of ZeroKnowledgeOnServedRequests.
  * The relation in the statements is ServedRequest: the model's result on the request is the
    claimed output. A request that is not served, and so every request at which the model has no
    result, enters the definition in one way only: proversAtFiles makes the provers refuse it, the
    field refuses of RunByRun asks that the online prover withholds at every message there, and
    the simulators are told of each request whether it is served
    (VerifiableInference/Final/ZeroKnowledgeBeforeHashing.lean).
  * Whether a request is served depends on the weights. The definition does not hide it: its
    simulators are told it for each request.
  * The definition asks that simulators exist. It puts no bound on their running time.
  * The statements are about the honest prover as it is defined in Lean, default values included.
    It is a definition, not a program that runs. It is not shown that the default values in that
    definition are never used. Nothing here is about the C++ programs.
  * The statements hold for the full-size layout alone (InScope: the layout file is that of the
    stored full-size example), and for the format's second hash function OnBytes.secondHashFunction alone.
  * The proofs in this file only combine theorems of other files. Every limit stated in the
    headers of AtFullSide/Honest/CompleteAtTheFiles.lean and
    AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean holds here too, among them: closed facts beneath
    are checked by evaluation in Lean's kernel, and no independent checker has replayed them.
  * The proofs beneath use theOneObjectValue (AtFullSide/Honest/TheOneObjectValue.lean), whose
    parameter open₂ is set to zeros. The statements of this file do not name that value or that
    parameter. It is not shown here that nothing depends on that choice.

Built on.
  * complete_in_scope (AtFullSide/Honest/CompleteAtTheFiles.lean).
  * zkOnServedRequests_inScope (AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean).
  * theProvers_eq (Johnson/CompletenessAndZeroKnowledge/TheProversEq.lean).
  * scope_named, live_named (E2E/CompleteAsIOPAtNamed.lean): the stored files are in scope and
    pass protocolDataWellFormed.
-/
import AtFullSide.Honest.CompleteAtTheFiles
import AtFullSide.E2E.ZeroKnowledgeFromTheRows
import Johnson.CompletenessAndZeroKnowledge.TheProversEq

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open OnBytes.Slice (frS)
open AtPublicFiles.Committed (PadZ pads_nonempty)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles settingsOfRead)
open FlashProve (committerCoinCountLessOne protocolDataWellFormed)
open OnBytes.Prover (CompleteAtEveryCoin)

local instance (priority := high) nonemptyPadZ_bothEnds : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_bothEnds : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_bothEnds : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy}

/-- Completeness on served requests and honest-verifier zero knowledge
(ZeroKnowledgeOnServedRequests) of the interactive oracle proof, with the equation between the two
ways of writing the provers, in one statement. The limits are in the header of this file. -/
theorem bothEnds_in_scope (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hr : readFiles Z = .ok pp) :
    (AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles Z (thePartsAt Z) hr ∧
      ∃ a c : ℝ≥0∞, a + 0 + c ≤ completenessTarget ∧
        CompleteAtEveryCoin (protocolAtFiles Z) (theProvers Z (settingsOfRead pp) (thePartsAt Z)) (workAtFiles Z)
          (ServedRequest committerCoinCountLessOne Z hr) a 0 c) ∧
      ZeroKnowledgeOnServedRequests Z hr
        (HonestProvers.ofThreeProvers (honestProvers Z (thePartsAt Z))) 0 0
        (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) ∧
      theProvers Z (settingsOfRead pp) (thePartsAt Z) =
        proversAtFiles Z hr (HonestProvers.ofThreeProvers (honestProvers Z (thePartsAt Z))) :=
  ⟨AtFullSide.Honest.complete_in_scope scope live hr, zkOnServedRequests_inScope scope live hr,
    theProvers_eq Z hr (thePartsAt Z)⟩

/-- The same at the stored full-size files, from their reading alone. Z is a variable with the
hypothesis Z = VerifierAndGoals.storedPublicFiles, so that the stored files' bytes are not unfolded here. -/
theorem bothEnds_at_the_stored_files (hZ : Z = VerifierAndGoals.storedPublicFiles) (hr : readFiles Z = .ok pp) :
    (AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles Z (thePartsAt Z) hr ∧
      ∃ a c : ℝ≥0∞, a + 0 + c ≤ completenessTarget ∧
        CompleteAtEveryCoin (protocolAtFiles Z) (theProvers Z (settingsOfRead pp) (thePartsAt Z)) (workAtFiles Z)
          (ServedRequest committerCoinCountLessOne Z hr) a 0 c) ∧
      ZeroKnowledgeOnServedRequests Z hr
        (HonestProvers.ofThreeProvers (honestProvers Z (thePartsAt Z))) 0 0
        (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) ∧
      theProvers Z (settingsOfRead pp) (thePartsAt Z) =
        proversAtFiles Z hr (HonestProvers.ofThreeProvers (honestProvers Z (thePartsAt Z))) :=
  bothEnds_in_scope (scope_named (Or.inl hZ)) (live_named (Or.inl hZ)) hr

end VerifiableInference.Compilation

#check @VerifiableInference.Compilation.bothEnds_in_scope
#print axioms VerifiableInference.Compilation.bothEnds_in_scope
#print axioms VerifiableInference.Compilation.bothEnds_at_the_stored_files
