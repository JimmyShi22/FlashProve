-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsView.lean: a step toward `pi_after`, a part of Run/PageIs.lean: the decision. Under the
hypotheses below, on the local transcript that the compiled verifier makes from the parser's
argument string, the protocol's decision is "the test bits pass, and dec says yes on the view of
what the lenient reader handed out".

One statement (`Run.PQ.Spec.pi_view`), proved, as stated here, in Run/PageIsViewProofs.lean. No
hash: the oracle functions do not occur; a hash function h is a parameter of the hypothesis
`LaxFacts h S o` and occurs nowhere else. Run/PageIs.lean compares two verifiers of a proof file,
the compiled verifier behind a lenient reader and the format's strict verifier. The compiled
verifier fills a transcript (`trP`, Run/ThinDefs.lean) from what its chain yields (the roots, the
verifier messages) and from the argument string's plain parts and openings, and evaluates the
protocol's decision on it.

Main names:
  `Spec.pi_view`: under `ok S = true` (the limits of the generic construction, Run/PlanQTypes.lean),
    `LaxFacts h S o`, the run's value, the typed plain parts pl of o's rounds, and verifier messages
    ρ whose view is what o says was drawn: the title's statement.

Why: the statement comes to this. The verifier messages read off the transcript are ρ. A round's
items on the transcript are o's items without the roots. For typing a message's items and reading
them back gives the items without the roots (`gots_ofGots`, Run/PageIsViewProofs.lean). And on this
transcript the "effective" plain part of a local round (`effP`, Run/ThinDefs.lean) is the plain
part. What was drawn is o's. The list "opened" of the typed view is the list of `openedOf`
(Fmt/M1View.lean). It is what is wanted, in the file's order (`pi_want`, Run/PageIsTab.lean). Each
column is read off the transcript's oracle message, which the verifier fills from the openings where
a root was sent.

Notation:
  `ex`: the external oracles, fixed before the protocol starts (`ExtSpec`, Iop/InteractiveOracleProof.lean);
  the `()` behind `accept`: the instance, of type `Unit` (`InteractiveOracleProof`, Iop/InteractiveOracleProof.lean);
  `(none, some none)`: what the chain yields for the round in front (`RtC`,
    Compile/Batch/Verifier.lean);
  the `()` before `pl`, `default` before `ρ`: the plain part and the verifier message of the round
    in front (`s0`, Run/PlanQS.lean).

Limits: this file says nothing on the chain, the walks or the strict format: the decision alone. It
says nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Run.PageIsTab

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

def Spec.pi_view : Prop :=
  ∀ (h : HId) (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
      (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool),
    ok S = true →
    ∀ (o : ChainOut) (run : ByteArray) (pl : Plains (uL C (rds S)))
        (ρ : Rho (uL C (rds S))) (ex : E0.Str),
      LaxFacts h S o → o.run = some run → plainsSL C (rds S) o.rounds.toList = some pl →
      drawnSL C (rds S) ρ = o.rounds.toList.map (·.drawn) →
      (PSof C (rds S) dec).accept () ex
          (trP (PSof C (rds S) dec).S (PSof C (rds S) dec).ann (wqS C K chal (rds S) dec).sh
            ((none, some none), rtSL C (rds S) o.rounds.toList) ((), pl) (default, ρ)
            (opensAt (TYS S C dec).up run o)) =
        (passSL C (rds S) ρ && dec (_root_.Fmt.viewOf S.firstTree o))

end Run.PQ
