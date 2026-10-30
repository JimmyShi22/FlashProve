-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SeatedSwitch.lean: AN ADDRESS THAT THE SEAT OF THE CODE
SWITCHES' OWN MESSAGES (`K2.switchSeat Z G`, Johnson/Desc/ProofFile/Honest/K2/OwnData.lean) SEATS IS
THE ADDRESS OF AN OWN MESSAGE OF ONE OF THE PLAN's SWITCHES (`p.ownAddr m`, p a member of
`K2.switchPlaces Z G`), AND ITS SEGMENT IS THE ONE INTO WHICH THAT SWITCH LEADS. On public data
alone; no premise but the seat's answer. No definition; one theorem.

What it is for. FillSwitch.lean (in this folder) speaks at an address `p.ownAddr m`; a caller that
holds only that an address is seated gets that form here. Its sister at the first segment's opening
is `seated_at_opening` (FillOpening.lean in this folder).

How. The seat is a search through the list that `K2.ownSeats` makes of the plan's switches, each
tried by `K1.momentSeat`: where the search answers, a member answers; that member's test says that
the sender is the switch's part and that the message's number is not below the switch's first own
one.

Limits. It says THAT such a p and m are there, not that they are the only ones: that the addresses
of the plan's switches are pairwise apart is not said here (it is a premise of the law on a seat
over a list in SeatReach.lean in this folder). Of the second number of the seat's answer nothing is
said. Nothing is evaluated at any plan.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5

/-- **A SEATED ADDRESS IS AN OWN MESSAGE's OF ONE OF THE PLAN's SWITCHES.** q: the seat's answer. -/
theorem seated_at_switch {Z : Pub} {G : Ground} {a : MsgAddr} {l m' : ℕ}
    (q : K2.switchSeat Z G a = some (l, m')) :
    ∃ p ∈ K2.switchPlaces Z G, ∃ m, a = p.ownAddr m ∧ l = p.link := by
  unfold K2.switchSeat K2.seatBy at q
  obtain ⟨x, hx, hq⟩ := List.exists_of_findSome?_eq_some q
  unfold K2.ownSeats at hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  have hq' : K1.momentSeat G.first.shape ⟨p.place, 0⟩ p.link 0 (1 + p.sizes.kept.length) a =
      some (l, m') := hq
  unfold K1.momentSeat at hq'
  split at hq'
  · rename_i hc
    obtain ⟨_, -, e⟩ := Option.map_eq_some_iff.1 hq'
    have hs : a.sender = ⟨p.place, 0⟩ := eq_of_beq hc.1
    have hm : 1 + p.sizes.kept.length ≤ a.msg := hc.2
    refine ⟨p, hp, a.msg - (1 + p.sizes.kept.length), ?_, (congrArg Prod.fst e).symm⟩
    cases a with
    | mk sd ms =>
      have hs' : sd = ⟨p.place, 0⟩ := hs
      have hm' : 1 + p.sizes.kept.length ≤ ms := hm
      subst hs'
      show (⟨⟨p.place, 0⟩, ms⟩ : MsgAddr) =
        ⟨⟨p.place, 0⟩, 1 + p.sizes.kept.length + (ms - (1 + p.sizes.kept.length))⟩
      congr 1
      omega
  · cases hq'

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.seated_at_switch
