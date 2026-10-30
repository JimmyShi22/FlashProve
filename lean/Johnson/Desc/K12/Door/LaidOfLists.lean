-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Door/LaidOfLists.lean: **THE LIST OF ROUNDS' SIDE OF THE FACT "seatsCarried", BROUGHT DOWN TO ONE EQUATION OF LISTS.** General in the codes, the planner's chain, the number of sub-protocols and what each is said to send. Statements and proofs.
What for. seats_at_cut (Johnson/IMR/SendsFold.lean) walks the fold and gives: the book's places and trees are a prefix of L, WHERE K12.Coin.laidOf codes ((List.range n).flatMap sn) = some L, sn j being what sub-protocol number j sends. The tables' constant has another L: the planner's own sendings, in the
order of their entries, laid (laidAtCodes, Johnson/Desc/K12/Door/LaidAt.lean). That the two are one follows from one equation of lists:
  SendsAre c n sn     the planner's sendings' notices, in the order of their entries, ARE the sub-protocols' sendings in the flat list's order.
  sendsAreB c n sn    the same as a test with code · sendsAre_of_B.
  **laid_of_lists**   SendsAre c n sn → laidAtCodes codes c = some Ld → K12.Coin.laidOf codes ((List.range n).flatMap sn) = some (toTree Ld): seats_at_cut's premise hL at L := toTree Ld.
Limits. The equation is a premise: it is shown at no list. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Door.DoorIs
import Johnson.Desc.K12.Door.LaidAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Door
open OnBytes OnBytes.Params

/-- The planner's sendings' notices, in the order of their entries, are the sub-protocols' sendings in the flat list's order. -/
def SendsAre (c : Johnson.G.ChainSends) (n : Nat) (sn : Nat → List (Array OracleNotice)) : Prop :=
  ((c.sends.mergeSort fun a b => a.entry ≤ b.entry).map fun x => x.sent.toArray) =
    (List.range n).flatMap sn

/-- The same as a test with code. -/
def sendsAreB (c : Johnson.G.ChainSends) (n : Nat) (sn : Nat → List (Array OracleNotice)) : Bool :=
  decide (((c.sends.mergeSort fun a b => a.entry ≤ b.entry).map fun x => x.sent.toArray) =
    (List.range n).flatMap sn)

theorem sendsAre_of_B {c : Johnson.G.ChainSends} {n : Nat} {sn : Nat → List (Array OracleNotice)}
    (h : sendsAreB c n sn = true) : SendsAre c n sn := by
  unfold sendsAreB at h
  unfold SendsAre
  exact of_decide_eq_true h

/-- **seats_at_cut's premise on the list, at the tables' own L.** -/
theorem laid_of_lists (codes : Codes) (c : Johnson.G.ChainSends) (n : Nat)
    (sn : Nat → List (Array OracleNotice)) (Ld : Laid) (hE : SendsAre c n sn)
    (hLd : laidAtCodes codes c = some Ld) :
    Coin.laidOf codes ((List.range n).flatMap sn) = some (toTree Ld) := by
  unfold SendsAre at hE
  unfold laidAtCodes at hLd
  have h := laidOf_is codes ((c.sends.mergeSort fun a b => a.entry ≤ b.entry).map (·.sent))
  rw [List.map_map, hLd] at h
  rw [← hE]
  exact h

end VerifiableInference.Desc.K12.Door

#print axioms VerifiableInference.Desc.K12.Door.sendsAre_of_B
#print axioms VerifiableInference.Desc.K12.Door.laid_of_lists
