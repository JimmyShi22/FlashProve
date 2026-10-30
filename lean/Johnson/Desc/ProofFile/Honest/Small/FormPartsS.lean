-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/FormPartsS.lean: `partsAt_of_thr`
(Honest/Small/FormParts.lean) FROM THE PAIR "the thread, and what is said" (`ThrS`,
Honest/Thread/Said.lean), what is said being a variable. One statement with its proof: a projection.

What it is not. Nothing proves that the pair holds at any run: the statement is CONDITIONAL on it.
General in the first chain's letters, in what is said and in the border. Nothing is claimed on
soundness, completeness or hiding.

  `partsAt_of_thrS`   CONDITIONAL on the pair at the border: no mark, and the eight clauses of the
                      table's promise that read the verifier's state

Written by the authors of the honest side of the output head's own rounds (K6), in the frame's
folder, not by the frame's authors.
All names stand in the namespace ProofFile.Honest.Small: a caller opens it.
-/
import Johnson.Desc.ProofFile.Honest.Small.FormParts
import Johnson.Desc.ProofFile.Honest.Thread.Said

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc.First (S)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **Wherever the thread holds and what is said stands: no mark, and the promise's clauses.** -/
theorem partsAt_of_thrS (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : ThrS L.thread Said b k s m E) :
    s.failed = none ∧ PartsAt L.N L.MgP L.links L.ps b (L.pubOf m.st.input.x, s) :=
  partsAt_of_thr L hT.1

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.partsAt_of_thrS
