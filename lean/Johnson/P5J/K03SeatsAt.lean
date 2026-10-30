-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03SeatsAt.lean: THE LOOKUPS' LEDGER's THREE DEBTS «some · sent · fits», AT ALL FIFTY PLACES, IN THE LEDGER's OWN TEXTS, FROM THE HEAD.
The ledger (Johnson/Desc/Sound/MgAt/K3Owed.lean: AttOwedR · LayOwedR · DigOwedR; K3Mean.lean: HeadRestR) asks at each lookup's place three sentences on the list of rounds: every message of the place's list is a member's (some); its seat is among the segment's sent tenants (sent); the seats fit what the IOP as written in Lean tells (fits).
  k03_calls_seats: at the calls' lookup of link l < 25, x := lookAt's place: the three, at 𝔇 := h.toAtMg.𝔇 h.𝔇, to the letter of AttOwedR | LayOwedR (and, at l = 24, of HeadRestR's hsome | hsent | hfits: 𝔇.l3.rad | 𝔇.l3.seat are 𝔇.rad3 | 𝔇.seat3 by unfolding).
  k03_digits_seats: the like at the digits' lookup, to the letter of DigOwedR at Dn := 𝔇.sent, L := 𝔇.l3, N := 𝔇.N, ms := 𝔇.ms, G := 𝔇.G.
FROM: the head's field k3 (At.k3SeatsB Zp cF Z.lay = true: ONE NAMED TEST: at every written link: the calls' and the digits' «some» and «sent») and its field plan.fit (P5T.seatsFitP …) through At.PlanOk.seatsFit.

Limits. It pays three debts of each of the fifty; the ledger's other debts stand. The two tests are FIELDS OF THE HEAD: evaluated true at the release's full-size public files and at the goals' second named set, with negative tests that reject (runs of a harness); no theorem gives them. Each theorem speaks where lookAt answers: EVALUATED: it answers at all 25 written links, at the calls' and at the digits' lookup, at both of these sets, and at link 25 at neither (a run of a harness); no theorem says so here. x enters the six sentences by x.link alone (callsSending | digSending | sigListCalls | digList read no other field).
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03Terms
import Johnson.P5J.SeatsFitAt
import Johnson.Desc.First.Look.K3CallsAddress

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt sigListCalls digList)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The calls' three, at every written link.** -/
theorem k03_calls_seats (h : AtMgA o Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt (At.X Zp) l false = some x) :
    (∀ i, ∃ y ∈ (h.toAtMg.𝔇 h.𝔇).ms, Alike y
      ⟨callsSending x (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3
        (fun j => (h.toAtMg.𝔇 h.𝔇).seat3 x.link false j.1), i⟩) ∧
    (∀ i : Fin (sigListCalls (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 x.link).length,
      (h.toAtMg.𝔇 h.𝔇).seat3 x.link false i.1 ∈ (h.toAtMg.𝔇 h.𝔇).N.sent l 0) ∧
    VerifiableInference.Desc.Sound.SeatFits (h.toAtMg.𝔇 h.𝔇).G (h.toAtMg.𝔇 h.𝔇).sent.codes
      (sigListCalls (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).rad3 x.link)
      (fun j => (h.toAtMg.𝔇 h.𝔇).seat3 x.link false j.1) := by
  have e := lookAt_link hx
  subst e
  obtain ⟨-, -, hs, ht, -, -⟩ := At.k3SeatsB_at Zp cF Z.lay h.k3 x.link hl
  exact ⟨At.calls_some Zp Z.lay x hs, At.calls_sent Zp cF Z.lay x x.link ht,
    At.calls_fits Zp Z.lay (F0T o Zp Np cF) x (At.PlanOk.seatsFit h.plan) hs⟩

/-- **The digits' three, at every written link.** -/
theorem k03_digits_seats (h : AtMgA o Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt (At.X Zp) l true = some x) :
    (∀ i, ∃ y ∈ (h.toAtMg.𝔇 h.𝔇).ms, Alike y
      ⟨digSending x (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad
        (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link true j.1), i⟩) ∧
    (∀ i : Fin (digList x (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad).length,
      ∃ t ∈ [2, 0, 1], (h.toAtMg.𝔇 h.𝔇).l3.seat x.link true i.1 ∈ (h.toAtMg.𝔇 h.𝔇).N.sent l t) ∧
    VerifiableInference.Desc.Sound.SeatFits (h.toAtMg.𝔇 h.𝔇).G (h.toAtMg.𝔇 h.𝔇).sent.codes
      (digList x (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3.rad)
      (fun j => (h.toAtMg.𝔇 h.𝔇).l3.seat x.link true j.1) := by
  have e := lookAt_link hx
  subst e
  obtain ⟨-, -, -, -, hs, ht⟩ := At.k3SeatsB_at Zp cF Z.lay h.k3 x.link hl
  have s1 := P5T.some_of_someB (At.ms Zp Z.lay) (At.digListAt Zp Z.lay x.link)
    (At.seat3At Zp x.link true) hs
  exact ⟨s1, fun i => P5T.sent_of_sentB (At.N Zp cF) x.link [2, 0, 1] _ (At.seat3At Zp x.link true) ht
      i.1 i.2,
    P5T.fits_of_some (F0T o Zp Np cF) (At.cs Zp) (At.ms Zp Z.lay) _ _ (At.PlanOk.seatsFit h.plan) s1⟩

end P5J

#print axioms P5J.k03_calls_seats
#print axioms P5J.k03_digits_seats
