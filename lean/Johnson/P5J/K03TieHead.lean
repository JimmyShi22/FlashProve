-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03TieHead.lean: THE KIND "LOOKUP" (K3): THE NAMED TEST tie (linkTieB,
  Johnson/Goal/Meaning/ReadingsOne.lean) AT ALL 25 SEGMENTS, FROM THE HEAD ALONE. One theorem.

  One call in another.
  k03_tie_head: k03_tie_of_names (Johnson/P5J/K03TieAt.lean: the test from the head and the names'
    tie at the segment) at names_tie_all (Johnson/P2LawR/NamesTieAll.lean: the
    names' tie at all 25 segments in scope: a join of three kinds' theorems: the feed-forward
    segments', the attention segments', the output head's).
Limits. The head is a premise. At OnBytes.secondHashFunction. The full size alone. The ledger's tie stands at
  (x.link, tl) off attAt | layAt: that these are (k, Meaning.tlAt X k) is the lookups' attAt_letters
  | layAt_letters: whoever joins calls them. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03TieAt
import Johnson.P2LawR.NamesTieAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.First.Look (idxAt)
open Meaning (linkTieB)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE TEST tie AT ALL 25 SEGMENTS, FROM THE HEAD ALONE.** -/
theorem k03_tie_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : ℕ} (hk : k < 25) :
    linkTieB (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 (At.num Zp)
      (idxAt (At.sentAt Zp) (At.num Zp) k) k (Meaning.tlAt (At.X Zp) k) = true :=
  k03_tie_of_names h hk fun _ hμ =>
    P2Law.Names.names_tie_all h.toAtMg.scope h.toAtMg.reads h.toAtMg.laid.pub hk hμ

end P5J

#print axioms P5J.k03_tie_head
#print axioms P2Law.Names.names_tie_all
