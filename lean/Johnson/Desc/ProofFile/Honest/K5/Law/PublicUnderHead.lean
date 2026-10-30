-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/PublicUnderHead.lean: FOUR TESTS WITH CODE ON PUBLIC DATA, AND
THE LIST OF THE SEGMENTS' PUBLIC DATA, AT EVERY CODE SWITCH OF THE PLAN, AT THE GROUND G THAT THE
BLANK GROUND RETURNS. FIVE LAWS OF THE CODE SWITCH's AUTHORS, CARRIED FROM THE GROUND OF THE HEAD's
OPENING TO G: SECOND STATEMENTS AT ANOTHER GROUND's NAME: NOTHING NEW IS PROVED. On public data
alone: no run, no input, no book. CONDITIONAL: under the hypothesis h, the library's head on the
public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean). No definition; five theorems: calls alone.

Main names, each under h and hG : blankBy pureRoad.links Zp = some G:
  `closing_under_head`: at every p of `K2.switchPlaces Zp G` the test `K2.closingOk` says yes, at
    the table `K2.freshTable` and the plan's own segments in front of p, `(K2.segmentsOf Zp G).take
    p.link`.
  `serves_under_head`, `roomy_under_head`, `fits_under_head`: at every such p: `p.sizes.serves`,
    `p.sizes.roomy`, `K2.placeFits p` say yes.
  `segments_under_head`: `K2.segmentsOf Zp G` is the written list `K2.Law.segsW`: so under h and hG
    it is not the empty list of that definition's arm "none" unless the written list is empty, on
    which nothing is said here.

How. The authors' laws (`K2.Law.closing_at_head`, Honest/K2/Law/ClosingAtHead.lean;
`serves_at_head`, `roomy_at_head`, `fits_at_head`, Honest/K2/Law/PublicAtHead.lean;
`segments_at_head`, Honest/K2/Law/PlacesWritten.lean) stand under their head and an opening, at the
opening's ground. Here the opening is taken out of h's own field `laid.opened`, and its ground is G,
by its field `blank` against hG: the two lines of `places_under_head` (MaskRowWritten.lean in this
folder).

Limits. The five say what tests with code and a list come to at the library's one plan: nothing on
what a closing leaves, nothing on what a prover sends. THE CLOSING's LAW RESTS ON CLOSED FACTS THAT
LEAN's KERNEL EVALUATES, IN ITS AUTHORS' FILES, UNDER LIFTED LIMITS ON DEPTH AND HEARTBEATS: they
are dear to build; this file replays none of them by another checker. The full size alone. At the
earlier hash `OnBytes.secondHashFunction`, a fixed function. Through its imports it stands above
Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a
fact on import lines.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtHead
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **The closing's test says yes at every switch of the plan, at the plan's own segments.**
CONDITIONAL: h; hG. -/
theorem closing_under_head
    {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) :
    ∀ p ∈ K2.switchPlaces Zp G, K2.closingOk K2.freshTable ((K2.segmentsOf Zp G).take p.link) p =
      true := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have e : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  rw [← e]
  exact K2.Law.closing_at_head h.toAtMg O

include h in
/-- **`serves` says yes at every switch of the plan.** CONDITIONAL: h; hG. -/
theorem serves_under_head
    {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) :
    ∀ p ∈ K2.switchPlaces Zp G, p.sizes.serves = true := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have e : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  rw [← e]
  exact K2.Law.serves_at_head h.toAtMg O

include h in
/-- **`roomy` says yes at every switch of the plan.** CONDITIONAL: h; hG. -/
theorem roomy_under_head
    {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) :
    ∀ p ∈ K2.switchPlaces Zp G, p.sizes.roomy = true := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have e : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  rw [← e]
  exact K2.Law.roomy_at_head h.toAtMg O

include h in
/-- **`K2.placeFits` says yes at every switch of the plan.** CONDITIONAL: h; hG. -/
theorem fits_under_head
    {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) :
    ∀ p ∈ K2.switchPlaces Zp G, K2.placeFits p = true := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have e : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  rw [← e]
  exact K2.Law.fits_at_head h.toAtMg O

include h in
/-- **The plan's segments are the written list.** CONDITIONAL: h; hG. -/
theorem segments_under_head
    {G : Ground}
    (hG : blankBy pureRoad.links Zp = some G) :
    K2.segmentsOf Zp G = K2.Law.segsW := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have e : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  rw [← e]
  exact K2.Law.segments_at_head h.toAtMg O

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.closing_under_head
#print axioms ProofFile.Honest.K5.serves_under_head
#print axioms ProofFile.Honest.K5.roomy_under_head
#print axioms ProofFile.Honest.K5.fits_under_head
#print axioms ProofFile.Honest.K5.segments_under_head
