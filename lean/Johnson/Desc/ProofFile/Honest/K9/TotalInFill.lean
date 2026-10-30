-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalInFill.lean: FOR THE ITEM "totalB": WHAT `TotalInBehind`
(Honest/K9/TotalFront.lean) SAYS, FROM FOUR NAMED FACTS ON THE STATE BEHIND THE BATCHING's STEP AND FOUR CLOSED FACTS
ON THE PLAN. A statement and its proof over the sealed library's law; no goal is stated.
  **`totalIn_fill`**   in the goals' scope, at the opening of the description, at a segment x.1 of the library's list
      of stretches, Lk the chain's link there, Xl the built segment, UNDER `LinkPlanFits Z x.1 Xl`
      (Johnson/Desc/First/Link/Law/HtinPaid.lean: four closed facts on the public part) and `N.groupAt x.1 = x.1`: AT
      EVERY STATE s' WITH: (h1) s' is reached at the border behind the batching · (h2) the public test on the ledger
      says yes (`First.ledgerB`) · (h3) the open ledger has a coefficient for each slot · (h4) the promise's test "the
      members are held" says yes at what is open there: wherever the link's runs behind return t: `K9.totalIn (N.group
      x.1) t = true`. The library's `htin_paid`, called at the condition "the state is s'"
The letter Fr and the value y stand for what the library's law carries beside a state (the oracles' strings of a
frame) and does not read: any frame with any value serves: a caller names one. No member; called by no line.
WHAT IS NOT CLAIMED. The four facts at any state. `LinkPlanFits` at any plan. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalFront
import Johnson.Desc.First.Link.Law.HtinPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem totalIn_fill {Fr : Sound.Frame} (y : Fr.E.Str) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Lk : Link S ProofFile.Cl} (eL : c.links[x.1]? = some Lk) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) (hP : LinkJoin.LinkPlanFits Z x.1 Xl) (N : Numbers)
    (hg : N.groupAt x.1 = x.1) (z : ProofFile.InstPub) (s' : S)
    (h1 : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 3 + x.2.2 + 1) (z, s'))
    (h2 : First.ledgerB s' = true) (h3 : ∀ G, s'.fork? = some G → G.LS.size = G.ns)
    (h4 : membersHeld N (IM.openAt IM.linksW IM.placesW (14 * x.1 + IM.nAt x.1 + 3)) s' = true) :
    ∀ t, Lk.runBehind s' = .ok t → Desc.K9.totalIn (N.group x.1) t = true := by
  intro t ht
  refine LinkJoin.htin_paid (α := Unit) (Fr := Fr) hS hR O hx eL e3 hP N hg z (fun a => a.1 = s')
    (fun a ha => ?_) (s', y) t rfl ⟨t, [], [], ⟨ht, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
  have e : a.1 = s' := ha
  rw [e]
  exact ⟨h1, h2, h3, h4⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.totalIn_fill
