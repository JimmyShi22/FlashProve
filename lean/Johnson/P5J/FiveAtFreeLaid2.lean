-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/FiveAtFreeLaid2.lean: five_at_free (Johnson/P5J/FiveAtFree.lean) WHERE THE PROOF FILE's
LIST OF ENTRY TESTS IS THE ONE OF THIRTEEN ROWS (LPFD.lawsAsk, Johnson/Desc/Laid/ProofAsks.lean;
GLOSSARY.md): THE HEAD PAYS THE PUBLIC TEST guard. IT IMPORTS ThirdParty/. One theorem: two calls.

WHICH VERIFIER. THE PROOF CALLS A LAW ON ROW 9 OF THE LIST (`LPFD.asks_made_at`). The head h names
the list by name, so h SAYS MORE than a yes of the list's first eight rows: the test stands in h.
A statement that is proved from this file speaks of a verifier that asks the thirteen rows.
[The list has fourteen rows: the thirteen and one more
(Johnson/Desc/Laid/ProofAsks.lean): so the head says that much more.]

  five_at_free_laid2   the head · the gate's accept · last · tables_fit → h.Five h.free (depthZ Z):
                       guard := LPFD.asks_made_at h.laid.asks h.laid.pub
                       (Johnson/Desc/Laid/ProofAsksForms.lean)
Limits. Those of FiveAtFree.lean. No soundness statement.
-/
import Johnson.P5J.FiveAtFree
import Johnson.Desc.Laid.ProofAsksForms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain)
open _root_.Run _root_.Run.PQ
open VerifierAndGoals FlashProve FlashProve VerifierAndGoals.AtTheName

variable {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

theorem five_at_free_laid2
    (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) {dB : RDT} {dt : List RDT} {r : Fmt.M1.Stage → ℕ}
    {Ld : VerifiableInference.Desc.K12.Door.Laid} (last : h.LastLeft dB dt r Ld)
    (tables_fit : h.TablesFitF h.free (depthZ Z)) : h.Five h.free (depthZ Z) :=
  five_at_free h hl
    ⟨LPFD.asks_made_at h.laid.asks h.laid.pub, last, tables_fit⟩

end P5J

#print axioms P5J.five_at_free_laid2
