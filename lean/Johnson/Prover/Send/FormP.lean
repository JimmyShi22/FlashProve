--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Prover/Send/FormP.lean: THE SHARED "SENDING", THE PROVER's SIDE: THE FORM's HALF AT THE
OTHER TEXT OF A SENDING: sendP groundG p false (Johnson/Desc/Ground/Calls.lean), which a code switch
calls: the answers are the FIRST items of a round in which the caller goes on. One statement and its
proof. (The switch's text names Ground.groundG, Johnson/Desc/Ground/Record.lean.)

  sendP_yes    SendFront, codes whose lengths are powers of two, a first round that shows no item
               and draws just the place's seeds, no factor of three words 0, and a second round
               whose first items hold the place's answers: sendP returns the numbers, the elements
               drawn, the answers, their count, AND THE SAME RECORD K1.behind, at the second round
               cut to the place's answers (K1.cutTo)

So the laws that are stated at K1.behind at all seeds and answers (Form.lean: behind_at,
behind_rest; Says.lean: send_says, old_says, send_claims, send_padded; Enc.lean) serve that text
too: no second set of laws.

By: send_yes_of (Form.lean); K1.sendP_of_cut (Johnson/Desc/K1/Law/SendP4.lean: a yes of K1's
decision at the cut round is a yes of sendP with the same record). The rows and the seeds of the two
texts are tied on the seal: K1.rowsFor_eq, K1.seedsOf_cut (SendP1.lean); the other direction:
K1.decide_of_sendP (SendP5.lean).

Limits. Nothing on what the caller does with the rest of the second round. Nothing on soundness, or
on what any entry shows or does not show.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Send.Form
import Johnson.Desc.K1.Law.SendP4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Send
open OnBytes OnBytes.Slice OnBytes.Means Cb VerifiableInference.Desc
open _root_.Desc.Plain (DState sendP groundG)

/-- **The text that a switch calls returns, with the same record.** -/
theorem sendP_yes {L : Type} (P : K1.Par) (d : DState L) (r₁ r₂ : Fmt.RoundView) (F : SendFront P d)
    (hl : P.codes.lengthsOk = true)
    (hdraw : (r₁.drawn.elems.map E.ofTriple).length = P.seeds * (P.coordinates + 1))
    (f1 : r₁.vals = []) (f2 : r₁.drawn.poss = []) (f3 : r₁.drawn.trits = [])
    (hz : ∀ s ∈ K1.seedsOf P r₁, isZeroE s.2 = false)
    (hn : (K1.answersIn (K1.cutTo P r₂)).length = P.answers) :
    sendP groundG P.gp false d P.sent r₁ r₂ =
      some (numbers P d.st.oracles.size, r₁.drawn.elems.map E.ofTriple,
        K1.answersIn (K1.cutTo P r₂), P.answers,
        K1.behind P d (K1.seedsOf P r₁) (K1.answersIn (K1.cutTo P r₂))) :=
  K1.sendP_of_cut P none d _ r₁ r₂ _ F.plan hl hdraw f1 f2 f3
    (send_yes_of P d r₁ (K1.cutTo P r₂) F hz hn)

end Johnson.Prover.Send

#print axioms Johnson.Prover.Send.sendP_yes
