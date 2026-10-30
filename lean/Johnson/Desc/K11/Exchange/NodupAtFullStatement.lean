-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/NodupAtFullStatement.lean: NO TWO MEMBERS OF THE FIRST CHAIN's FLAT LIST
STAND AT ONE PLACE: STATEMENTS ALONE: two, each a definition of a proposition. NOTHING IS PROVED IN
THIS FILE, and neither is one of the library's goals: they are lemmas' statements. The texts are the
description's; no prover is named.

  `PlacesNodup`   at every description of a file that passes the library's test on places
                  (`FileDescription.placesOk`, Johnson/Desc/Block.lean: each triple of chain, link and
                  number is counted once over the three chains' flat lists): the places of the first
                  chain's flat list are pairwise different
  `NodupAtFull`   under the library's one hypothesis at the full size (`P5J.AtMgA`,
                  Johnson/P5J/MgAtAll.lean): the same of its first chain cF

Limits. The hypothesis is a premise: it is shown at no file here; it stands at the earlier hash.
Nothing on any property.
-/
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open VerifiableInference.Desc (Chain FileDescription)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- The statement at every description. Not proved here; a lemma's statement, none of the library's
goals. -/
def PlacesNodup : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi), F.placesOk = true → (F.first.blocksInOrder.map (·.place)).Nodup

/-- The statement under the one hypothesis. The letters: its own. Not proved here; a lemma's
statement, none of the library's goals. -/
def NodupAtFull : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S Cl) (x : VerifiableInference.Desc.First.Look.Place),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x → (cF.blocksInOrder.map (·.place)).Nodup

end Johnson.Desc.First.ForkMerge.Exchange
