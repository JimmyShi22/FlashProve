-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OneIsTypedFull.lean: the run of the compiled verifier over the single oracle on bit strings
(`run1W`, Run/PageQFull.lean) is its run at the typed oracle functions written from the format
(`runFullC`, Run/PlanQSF.lean), on every file, outcome for outcome, for every description and number
of blocks that pass three tests. Both runs are of the generic construction, at the wiring with whole
paths, and both read the file with the parser that fills whole paths.

Three statements (each a `Prop` in `Run.PQ.Spec`); the proofs are in Run/OneIsTypedFullProofs.lean.
The run over the single oracle goes through the encoding of the queries, all blocks asked. With
whole paths each opened leaf has an authentication path of its own. This file is the analogue of
Run/OneIsTypedTop.lean, which says the same of the run functions behind the lenient reader at the
wiring with pruned openings (`run1C` = `runLaxC`). Many statements of this library are written
twice: a definition in the namespace `Spec` states a proposition, and a theorem of the same name
outside that namespace proves it (lean/GLOSSARY.md).

Main names: `Spec.oneW_is_typed`, `Spec.oneW_pull`, `Spec.oneW_ck`. The first is an equation between
outcomes. An outcome is the first stage that refuses, or accepted: `.limits`, `.reader`,
`.verifier`, `.accepted` (`Who`, Run/PlanQRun.lean).

The three tests can be run: `ok` (Run/PlanQTypes.lean), `OKQ` (Run/PageQ.lean), `fourBounds`
(Run/OneIsTypedTop.lean). The first three bounds of `fourBounds` are what the encoding of the
queries needs so that numbers can be spelled in their words; the fourth follows from `ok S = true`
(`Fmt.ok_count`). The bounds are wider than the format's own bounds.

Why: what it joins. On the one side: under `ok S`, `OKQ S` and a test on the description and the
file (`smallF S file`), the verdict of `run1W` is the definition's run (`ZKCP.OComp.run`,
ZKCP/Defs.lean) of a tree of queries (`Spec.run1W_is`, Run/Run1Full.lean [not in this library]). On the other side: the
verifier of `runFullC` is the run of `Compile.Batch.verifyOneProtocol` at typed oracle functions (`vpfc_eq`,
Run/PlanQSF.lean). At three closed descriptions, each with the first toy's decision (`Fmt.M1.dec`),
with challenges as hash blocks, that verifier is the run of `Compile.Batch.vBS` at a wiring
(Run/M1RunTiePF.lean). Of that wiring the conditions on that one protocol's wiring (`OKG`) are
proved in the same file. What is not claimed there stands in part 4 of that file's head.

Notation:
  `C`: a choice of challenge types: for each round the type of the verifier's message
    (Run/PlanQS.lean);
  `K`: the number of blocks from which a verifier message is made;
  `chal`: the samplers, from `K` 256-bit blocks to a verifier message;
  `dec`: a decision: a function `View → Bool`;
  `kOf S`: the blocks of a verifier's message, the greatest number over the rounds
    (Run/PlanQRun.lean);
  `run1WF`: `run1W` in the form that runs (Run/PageQFull.lean);
  `run1WPF`, `runFullSP`: `run1WF`, `runFullC` at `ckP`, `kOf S`, `chalP` (Run/PageQFull.lean,
    Run/PlanQSFP.lean);
  `runFullS`: `runFullC` at `ck`, `kOf S`, `chalOf` (Run/PlanQSF.lean).

Limits: that either run is "the scheme's verifier", or sound: no. This file says nothing on the
strict reader's runs. It does not say that the two wirings, or the two parsers, give one verdict.
(Not said in this file. See `Spec.full_lax` and `Spec.fullOne_lax`, stated in Run/PageIsFull.lean [not in this library]
under hypotheses that are stated there.) It stands at the leaves' label as Run/PageQChain.lean and
Run/PlanQS.lean spell it, through Run/PageQFit.lean and Run/OneIsTypedLeaf.lean alone.

Terms: lean/GLOSSARY.md.
-/
import Run.OneIsTypedTop
import Run.PageQFull
import Run.PlanQSFP

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch
namespace Spec

/-- States: if `ok S`, `OKQ S` and `fourBounds S K` hold, the run over the single oracle is the run
at the typed oracle functions, including who decided, on every file. -/
def oneW_is_typed : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (dec : View → Bool) (file : ByteArray),
    ok S = true → OKQ S = true → fourBounds S K = true →
    run1W S C K chal dec file = runFullC S C K chal dec file

/-- States the same at the choice `ckP` (challenges as hash blocks), of the forms written for a
toy's full parameters. -/
def oneW_pull : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray), ok S = true → OKQ S = true →
    fourBounds S (kOf S) = true → run1WPF S dec file = runFullSP S dec file

/-- States the same at the choice `ck` (challenges as sampled values). -/
def oneW_ck : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray), ok S = true → OKQ S = true →
    fourBounds S (kOf S) = true →
    run1WF S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec file = runFullS S dec file

end Spec
end Run.PQ
