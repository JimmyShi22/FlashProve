-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/DescriptionTie.lean: THE TIE TO THE GOALS' VERIFIER, BY THEOREMS. The configuration `Cz Z`, the
three protocols `filesAt Z` (E2E/ObjectAtFiles.lean) and the placeholder provers ARE the
configuration, the three protocols and the provers of the IOP as written in Lean, where all goals
but two read it (`VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription`, Johnson/Goal/Description/Description.lean);
and the object in the input at which `VerifierAndGoals.verify` calls the compiled verifier is `(filesAt Z).withProvers
(filesAt Z).fixedMessageProvers`.

Why. E2E/ObjectAtFiles.lean writes `filesAt Z` from the letters `dataAtFiles flashProveData Z`. That these are
the letters of the value of which the goals speak is shown here.

Definitions.
  `partsOf D Z`: the configuration of a value D of the library's type `Description`, its three
    protocols and provers at Z, as one value.
  `objectOf r`: an input's index type, instance type and object, as one value.
What is shown.
  `parts_built`: `partsOf (descriptionOfDataOnBytes flashProveData) Z` is (`Cz Z`, `filesAt Z`, the placeholder provers):
    by unfolding.
  `parts_description`: the same of `atSecondHashFunction theDescription`: by the library's `ofBuilt`.
  `object_built`, `object_description`: at every digest c and further reading m, the object of the
    input `D.input Z c m` is (`FullSizeMatrix`, `XF`, `(filesAt Z).withProvers (filesAt Z).fixedMessageProvers`).
  `verify_calls`: `VerifierAndGoals.verify D Z parse` is, by its definition: if Z is in scope, parse, read the
    digest c, read m, and call `innerCompiledVerifier (D.input Z c m)`; else reject. For every D of the type
    `Description`.

WHAT THE TIE BUYS, AND WHAT NOT. The compiled verifier reads the object through its verifier's side
alone (`HolographicProtocol.v`, Hiop/RecSide.lean; `innerCompiledVerifier_eq`, Johnson/Top/InnerCompiledVerifierSide.lean): word length,
symbols, the types of OOD seeds and answers, the three protocols, the number of requests in a batch,
and the two maps on instances (`early`, `late`). THE ENCODER, THE PADS, THE ENCODING RANDOMNESS AND
THE MAP TO THE OOD ANSWERS ARE NOT READ BY IT: re-indexing along any map f lays the encoder's
composition with f in the encoder's field, a constant map among them, and the compiled verifier is
the same function, key and proof being passed through their verifier's side (E2E/SameVerifier.lean).
What makes them the protocol's is: that they are fields of the IOP as written in Lean; the decoder's
clause at the matrices in range (from an honest table and its OOD sample the index decoder returns
the index); and a reading of the format's pages that is not machine-checked. Not the verifier.

Limits.
- Equations of values; nothing on soundness, completeness or what a view shows.
- WHAT THE TWO VALUES DROP. `partsOf` holds three of a `Description`'s fields; it drops the
  compiler's further letters (`T`), the further public reading, the extractor, what a proof may
  reveal, the honest committer and prover with their randomness, the form and the parser. `objectOf`
  holds three of an input's fields; it drops what a query's body may hold beside (`LeafBody`), the marks
  of the rounds, the wires, how the OOD answers are written as digests (`answerCode`), the fixed OOD sample
  that fills a session's first query (`fixedSample`), the parameters (`compilerParameters`), the coding of queries into the
  one hash function, the code of a key, how an instance is built from tokens, the model, and the
  honest side's algorithms. Nothing is said of these here.
- `atSecondHashFunction`: the IOP as written in Lean at the format's second hash function (our second,
  non-standard hash, built on BLAKE2b's compression function). At another function in that place
  nothing is said.
- The object here has EVERY matrix as index. `objAt Z P` is that object cut to the matrices in
  range, with any provers (E2E/ObjectAtFiles.lean; E2E/SameVerifier.lean for the compiled verifier).

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
import E2E.ObjectAtFiles
import Johnson.Goal.Description.Description

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Hiop
open OnBytes.Flat (Files)
open VerifiableInference VerifiableInference.OnPublicFiles
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles Description atSecondHashFunction theDescription)
open FlashProve (descriptionOfDataOnBytes)
open FlashProve (flashProveData)

/-- The configuration, three protocols and provers at Z of a value of the type `Description`, as one
value. -/
def partsOf (D : Description) (Z : PublicFiles) : Σ C : ConfigurationWithOutOfDomainSample, Σ F : Files C, F.Provers :=
  ⟨D.C Z, D.F Z, D.P Z⟩

/-- An input's index type, instance type and object, as one value. -/
def objectOf (r : InnerCompilerInput) : Σ I : Type, Σ X : Type, HolographicProtocol I X := ⟨r.Index, r.Instance, r.protocol⟩

/-- **The parts at Z of the value that the library builds are ours**: by unfolding. -/
theorem parts_built (Z : PublicFiles) :
    partsOf (descriptionOfDataOnBytes flashProveData) Z = ⟨Cz Z, filesAt Z, (filesAt Z).fixedMessageProvers⟩ := rfl

/-- **So are the parts of the IOP as written in Lean, where all goals but two read it.** -/
theorem parts_description (Z : PublicFiles) :
    partsOf (atSecondHashFunction theDescription) Z = ⟨Cz Z, filesAt Z, (filesAt Z).fixedMessageProvers⟩ :=
  VerifierAndGoals.ofBuilt (Q := fun D => partsOf D Z = ⟨Cz Z, filesAt Z, (filesAt Z).fixedMessageProvers⟩) (parts_built Z)

/-- The object of the built value's input, at every digest and further reading. -/
theorem object_built (Z : PublicFiles) (c : Digest) (m : (descriptionOfDataOnBytes flashProveData).More) :
    objectOf ((descriptionOfDataOnBytes flashProveData).input Z c m) = ⟨FullSizeMatrix, XF, (filesAt Z).withProvers (filesAt Z).fixedMessageProvers⟩ := rfl

/-- **The object in the input at which the goals' verifier calls the compiled verifier.** -/
theorem object_description (Z : PublicFiles) :
    ∀ (c : Digest) (m : (atSecondHashFunction theDescription).More),
      objectOf ((atSecondHashFunction theDescription).input Z c m) =
        ⟨FullSizeMatrix, XF, (filesAt Z).withProvers (filesAt Z).fixedMessageProvers⟩ :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : Digest) (m : D.More),
      objectOf (D.input Z c m) = ⟨FullSizeMatrix, XF, (filesAt Z).withProvers (filesAt Z).fixedMessageProvers⟩)
    (object_built Z)

/-- **What the goals' verifier is, by its definition**, for every D of the type `Description`: if Z
is in scope: parse, read the digest c of the public files, make the further reading m, and call the
compiled verifier at the input `D.input Z c m`; else reject. -/
theorem verify_calls (D : Description) (Z : PublicFiles) {Form : Type} (parse : VerifierAndGoals.Parser D Z Form)
    (commitment : Commitment) (prompt output : List Token) (form : Form) :
    VerifierAndGoals.verify D Z parse commitment prompt output form =
      if VerifierAndGoals.InScope Z then
        VerifierAndGoals.andThen (parse prompt output form) fun proof =>
          VerifierAndGoals.andThen (VerifierAndGoals.readConfig Z) fun c =>
            VerifierAndGoals.andThen (D.readMore Z c) fun m =>
              innerCompiledVerifier (D.input Z c m) commitment prompt output proof
      else .done false := rfl

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.verify_calls
#print axioms AtPublicFiles.AtFiles.parts_built
#print axioms AtPublicFiles.AtFiles.parts_description
#print axioms AtPublicFiles.AtFiles.object_built
#print axioms AtPublicFiles.AtFiles.object_description
